# Reframe court

Raw observations live in the hash-chained `.autoresearch/measurements.jsonl`; this file keeps
only durable ontology changes and forward predictions.

## RF-001 — artifact and Fiat–Shamir draw are one state

- **Previous ontology:** the zero scorer floor might be attained by encoding the finite 9,024
  verifier inputs as a free-classical lookup.
- **Why incomplete:** the table artifact changes the complete semantic operation stream, which
  is the Fiat–Shamir seed; the dataset cannot be held fixed independently of the candidate.
- **Discriminator:** exact frozen-dataset construction followed by an exact self-seeded 9,024-pair
  census in `repro/zero_score_lookup.py`.
- **Observation:** 27 prefix bits uniquely selected all frozen inputs; 3,042,193 X/condition ops
  fit the cap and had zero frozen failures, but the candidate stream had zero table hits and
  9,024 self-seeded classical failures.
- **Compression:** artifact identity and verifier draw are one endogenous, content-addressed state.
- **Forward prediction:** a table derived from another stream will have negligible overlap after
  reseeding. An attainable `H0-zero-rounding` construction must instead be seed-independent,
  solve a semantic-stream fixed point, or generically extract/transform the quantum inputs.
- **Status:** previous ontology refuted; prediction retained for the next H0 discriminator.
