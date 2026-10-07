#!/usr/bin/env python3
"""Deterministic global search for an exact eight-shear joint codec.

This is a witness finder, not an UNSAT procedure. It searches beyond the closed
one-shear neighborhoods by evolving arbitrary valid generalized shears. For each
nonlinear prefix it solves the best final affine output map exactly over the 25
reachable pair states.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import y5_joint_codec_synth as joint
import y5_normalizer_synth as synth

Shear = tuple[int, int, int, int]
Sequence = tuple[Shear, ...]


@dataclass(frozen=True)
class Evaluation:
    errors: int
    output_rank: int
    outputs: tuple[int, ...]

    @property
    def fitness(self) -> tuple[int, int, int]:
        rank_deficit = synth.WIDTH - self.output_rank
        return self.errors + 8 * rank_deficit, self.errors, rank_deficit


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _columns(values: list[int], width: int) -> tuple[int, ...]:
    return tuple(
        sum(((value >> bit) & 1) << index for index, value in enumerate(values))
        for bit in range(width)
    )


def _affine_mask(coefficients: int, columns: tuple[int, ...], all_rows: int) -> int:
    result = all_rows if coefficients & 1 else 0
    linear = coefficients >> 1
    while linear:
        bit = (linear & -linear).bit_length() - 1
        result ^= columns[bit]
        linear &= linear - 1
    return result


def apply_sequence(sequence: Sequence, initial: tuple[int, ...], all_rows: int) -> tuple[int, ...]:
    columns = list(initial)
    for left, right, direction, offsets in sequence:
        left_mask = _affine_mask((left << 1) | (offsets & 1), tuple(columns), all_rows)
        right_mask = _affine_mask((right << 1) | ((offsets >> 1) & 1), tuple(columns), all_rows)
        toggle = left_mask & right_mask
        changed = direction
        while changed:
            bit = (changed & -changed).bit_length() - 1
            columns[bit] ^= toggle
            changed &= changed - 1
    return tuple(columns)


def _best_affine_options(
    columns: tuple[int, ...], target: int, all_rows: int
) -> tuple[int, tuple[int, ...]]:
    best = len(columns) * all_rows.bit_count() + 1
    options: list[int] = []
    for coefficients in range(1 << (len(columns) + 1)):
        distance = (_affine_mask(coefficients, columns, all_rows) ^ target).bit_count()
        if distance < best:
            best = distance
            options = [coefficients]
        elif distance == best:
            options.append(coefficients)
    return best, tuple(options)


def _best_ranked_outputs(options: list[tuple[int, ...]], width: int) -> tuple[int, tuple[int, ...]]:
    best_rank = -1
    best: tuple[int, ...] = ()
    combinations = 1
    for values in options:
        combinations *= len(values)
    if combinations <= 100_000:
        candidates = itertools.product(*options)
    else:
        candidates = (tuple(values[0] for values in options),)
    for candidate in candidates:
        rank = synth.matrix_rank([coefficients >> 1 for coefficients in candidate], width)
        if rank > best_rank:
            best_rank = rank
            best = tuple(candidate)
            if rank == width:
                break
    return best_rank, best


def evaluate_sequence(
    sequence: Sequence,
    initial_columns: tuple[int, ...],
    target_columns: tuple[int, ...],
    all_rows: int,
) -> Evaluation:
    columns = apply_sequence(sequence, initial_columns, all_rows)
    errors = 0
    options: list[tuple[int, ...]] = []
    for target in target_columns:
        distance, coefficients = _best_affine_options(columns, target, all_rows)
        errors += distance
        options.append(coefficients)
    rank, outputs = _best_ranked_outputs(options, len(columns))
    return Evaluation(errors=errors, output_rank=rank, outputs=outputs)


def _directions(left: int, right: int, width: int) -> tuple[int, ...]:
    return tuple(
        direction
        for direction in range(1, 1 << width)
        if synth.dot(left, direction) == 0 and synth.dot(right, direction) == 0
    )


def random_shear(rng: random.Random, width: int) -> Shear:
    left = rng.randrange(1, 1 << width)
    right = rng.randrange(1, 1 << width)
    while right == left:
        right = rng.randrange(1, 1 << width)
    offsets = rng.randrange(4)
    if left > right:
        left, right = right, left
        offsets = ((offsets & 1) << 1) | ((offsets >> 1) & 1)
    direction = rng.choice(_directions(left, right, width))
    return left, right, direction, offsets


def mutate(sequence: Sequence, rng: random.Random, width: int) -> Sequence:
    result = list(sequence)
    index = rng.randrange(len(result))
    left, right, direction, offsets = result[index]
    mode = rng.randrange(10)
    if mode < 4:
        result[index] = random_shear(rng, width)
    elif mode < 6:
        choices = [value for value in range(4) if value != offsets]
        result[index] = left, right, direction, rng.choice(choices)
    elif mode < 8:
        directions = [value for value in _directions(left, right, width) if value != direction]
        result[index] = left, right, rng.choice(directions), offsets
    else:
        result[index] = random_shear(rng, width)
        other = rng.randrange(len(result))
        result[other] = random_shear(rng, width)
    if rng.random() < 0.08:
        first, second = rng.sample(range(len(result)), 2)
        result[first], result[second] = result[second], result[first]
    return tuple(result)


def _from_program(program: dict[str, Any]) -> Sequence:
    sequence: list[Shear] = []
    for shear in program["shears"]:
        left = synth.vector(shear["left"][1:])
        right = synth.vector(shear["right"][1:])
        offsets = shear["left"][0] | (shear["right"][0] << 1)
        if left > right:
            left, right = right, left
            offsets = ((offsets & 1) << 1) | ((offsets >> 1) & 1)
        sequence.append((left, right, synth.vector(shear["direction"]), offsets))
    return tuple(sequence)


def _to_program(sequence: Sequence, outputs: tuple[int, ...], width: int) -> dict[str, Any]:
    return {
        "width": width,
        "shears": [
            {
                "enabled": 1,
                "left": [offsets & 1, *[(left >> bit) & 1 for bit in range(width)]],
                "right": [
                    (offsets >> 1) & 1,
                    *[(right >> bit) & 1 for bit in range(width)],
                ],
                "direction": [(direction >> bit) & 1 for bit in range(width)],
            }
            for left, right, direction, offsets in sequence
        ],
        "outputs": [
            [coefficients & 1, *[((coefficients >> 1) >> bit) & 1 for bit in range(width)]]
            for coefficients in outputs
        ],
    }


def search(
    *,
    evaluation_budget: int,
    seed: int,
    population_size: int = 256,
    elite_size: int = 32,
) -> dict[str, Any]:
    if evaluation_budget < population_size:
        raise ValueError("evaluation budget must cover the initial population")
    rng = random.Random(seed)
    joint_ops, table = joint.configure_problem()
    width = joint.WIDTH
    domain = list(joint.PAIR_INPUTS)
    targets = [table[value] for value in domain]
    initial_columns = _columns(domain, width)
    target_columns = _columns(targets, width)
    all_rows = (1 << len(domain)) - 1
    reference = _from_program(synth.reference_program(joint_ops))
    if len(reference) != joint.REFERENCE_CCX_COUNT:
        raise AssertionError("reference shear count changed")

    seeds: list[Sequence] = [reference[:index] + reference[index + 1 :] for index in range(len(reference))]
    while len(seeds) < population_size:
        if len(seeds) < population_size * 3 // 4:
            base = rng.choice(seeds[: len(reference)])
            for _ in range(1 + rng.randrange(4)):
                base = mutate(base, rng, width)
            seeds.append(base)
        else:
            seeds.append(tuple(random_shear(rng, width) for _ in range(8)))

    cache: dict[Sequence, Evaluation] = {}
    evaluated = 0

    def measured(sequence: Sequence) -> Evaluation:
        nonlocal evaluated
        if sequence not in cache:
            cache[sequence] = evaluate_sequence(
                sequence, initial_columns, target_columns, all_rows
            )
            evaluated += 1
        return cache[sequence]

    population = list(dict.fromkeys(seeds))
    history: list[dict[str, int]] = []
    best_sequence = population[0]
    best_evaluation = measured(best_sequence)
    generation = 0
    while evaluated < evaluation_budget:
        population.sort(key=lambda sequence: measured(sequence).fitness)
        current = population[0]
        current_evaluation = measured(current)
        if current_evaluation.fitness < best_evaluation.fitness:
            best_sequence = current
            best_evaluation = current_evaluation
            history.append(
                {
                    "generation": generation,
                    "evaluations": evaluated,
                    "errors": best_evaluation.errors,
                    "output_rank": best_evaluation.output_rank,
                }
            )
        if best_evaluation.errors == 0 and best_evaluation.output_rank == width:
            break
        exploit = population[: elite_size // 2]
        explore = rng.sample(population[elite_size // 2 :], elite_size - len(exploit))
        elites = [*exploit, *explore]
        next_population: list[Sequence] = list(elites)
        seen = set(next_population)
        while len(next_population) < population_size and evaluated < evaluation_budget:
            if rng.random() < 0.20:
                first, second = rng.sample(elites, 2)
                cut = rng.randrange(1, len(first))
                child = first[:cut] + second[cut:]
            else:
                child = mutate(rng.choice(elites), rng, width)
            if child in seen:
                continue
            seen.add(child)
            next_population.append(child)
            measured(child)
        population = next_population
        generation += 1

    population.sort(key=lambda sequence: measured(sequence).fitness)
    if measured(population[0]).fitness < best_evaluation.fitness:
        best_sequence = population[0]
        best_evaluation = measured(best_sequence)
    program = _to_program(best_sequence, best_evaluation.outputs, width)
    witness: dict[str, Any] | None = None
    if best_evaluation.errors == 0 and best_evaluation.output_rank == width:
        symbolic, compiled, compiled_verification = joint.verify_candidate(program, table, 8)
        if symbolic["verdict"] != "green" or compiled_verification["verdict"] != "green":
            raise AssertionError("zero-residual stochastic witness failed exact replay")
        witness = {
            "program": program,
            "compiled_operations": compiled,
            "symbolic_verification": symbolic,
            "compiled_verification": compiled_verification,
            "rust_table": synth.rust_table(compiled),
        }
    return {
        "schema_version": 1,
        "scope": "unrestricted exact-eight generalized-shear witness search",
        "status": "witness" if witness is not None else "unresolved",
        "seed": seed,
        "evaluation_budget": evaluation_budget,
        "evaluations": evaluated,
        "generations": generation,
        "population_size": population_size,
        "elite_size": elite_size,
        "reference_shears": len(reference),
        "best": {
            "errors": best_evaluation.errors,
            "output_rank": best_evaluation.output_rank,
            "program": program,
        },
        "improvement_history": history,
        "witness": witness,
        "warning": "No witness is not evidence of UNSAT.",
        "source_hashes": {
            "y5_joint_codec_synth.py": _sha256(Path(joint.__file__)),
            "y5_normalizer_synth.py": _sha256(Path(synth.__file__)),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evaluations", type=int, default=200_000)
    parser.add_argument("--seed", type=int, default=0xECDA5A)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = search(evaluation_budget=args.evaluations, seed=args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "best"}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
