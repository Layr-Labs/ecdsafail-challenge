#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

constexpr std::uint32_t kConstant = 0x01ffffffU;
constexpr std::size_t kStateWords = 6;
constexpr std::size_t kHyperplaneWords = 5;
constexpr std::uint32_t kNormals = 31;

using State = std::array<std::uint32_t, kStateWords>;
using Hyperplane = std::array<std::uint32_t, kHyperplaneWords>;
using Coordinates = std::array<std::uint32_t, 5>;

struct HashRef {
    std::uint64_t hash;
    std::uint32_t ref;
};

struct Basis {
    std::array<std::uint32_t, 32> rows{};
    int rank = 0;

    bool insert(std::uint32_t value) {
        for (int pivot = 31; pivot >= 0; --pivot) {
            if (((value >> pivot) & 1U) != 0 && rows[pivot] != 0) {
                value ^= rows[pivot];
            }
        }
        if (value == 0) {
            return false;
        }
        const int pivot = 31 - std::countl_zero(value);
        for (int other = 0; other < 32; ++other) {
            if (rows[other] != 0 && ((rows[other] >> pivot) & 1U) != 0) {
                rows[other] ^= value;
            }
        }
        rows[pivot] = value;
        ++rank;
        return true;
    }

    bool contains(std::uint32_t value) const {
        for (int pivot = 31; pivot >= 0; --pivot) {
            if (((value >> pivot) & 1U) != 0 && rows[pivot] != 0) {
                value ^= rows[pivot];
            }
        }
        return value == 0;
    }
};

std::vector<State> read_states(const std::string& path) {
    std::ifstream input(path, std::ios::binary | std::ios::ate);
    if (!input) {
        throw std::runtime_error("cannot open " + path);
    }
    const auto bytes = input.tellg();
    constexpr std::streamoff record_bytes = static_cast<std::streamoff>(sizeof(State));
    if (bytes < 0 || bytes % record_bytes != 0) {
        throw std::runtime_error("invalid frontier byte length for " + path);
    }
    std::vector<State> states(static_cast<std::size_t>(bytes / record_bytes));
    input.seekg(0);
    input.read(reinterpret_cast<char*>(states.data()), bytes);
    if (!input) {
        throw std::runtime_error("short read from " + path);
    }
    return states;
}

Coordinates state_coordinates(const State& state) {
    Basis basis;
    if (!basis.insert(kConstant)) {
        throw std::runtime_error("constant basis insertion failed");
    }
    Coordinates coordinates{};
    std::size_t count = 0;
    for (const auto row : state) {
        if (basis.insert(row)) {
            if (count >= coordinates.size()) {
                throw std::runtime_error("state rank exceeds six");
            }
            coordinates[count++] = row;
        }
    }
    if (count != coordinates.size() || basis.rank != 6) {
        throw std::runtime_error("frontier state does not have affine rank six");
    }
    return coordinates;
}

std::array<std::array<std::uint8_t, 4>, kNormals> invariant_bases() {
    std::array<std::array<std::uint8_t, 4>, kNormals> result{};
    for (std::uint32_t normal = 1; normal <= kNormals; ++normal) {
        Basis basis;
        std::size_t count = 0;
        for (std::uint32_t form = 1; form <= kNormals && count < 4; ++form) {
            if ((std::popcount(form & normal) & 1) != 0) {
                continue;
            }
            if (basis.insert(form)) {
                result[normal - 1][count++] = static_cast<std::uint8_t>(form);
            }
        }
        if (count != 4) {
            throw std::runtime_error("failed to construct invariant hyperplane basis");
        }
    }
    return result;
}

std::uint32_t linear_mask(const Coordinates& coordinates, std::uint32_t form) {
    std::uint32_t value = 0;
    for (std::size_t index = 0; index < coordinates.size(); ++index) {
        if (((form >> index) & 1U) != 0) {
            value ^= coordinates[index];
        }
    }
    return value;
}

Hyperplane canonical_hyperplane(const Coordinates& coordinates,
                                const std::array<std::uint8_t, 4>& forms) {
    Basis basis;
    basis.insert(kConstant);
    for (const auto form : forms) {
        basis.insert(linear_mask(coordinates, form));
    }
    if (basis.rank != 5) {
        throw std::runtime_error("hyperplane rank is not five");
    }
    Hyperplane result{};
    std::size_t index = 0;
    for (int pivot = 31; pivot >= 0; --pivot) {
        if (basis.rows[pivot] != 0) {
            result[index++] = basis.rows[pivot];
        }
    }
    if (index != result.size()) {
        throw std::runtime_error("canonical hyperplane has wrong size");
    }
    return result;
}

std::uint64_t mix64(std::uint64_t value) {
    value ^= value >> 30;
    value *= 0xbf58476d1ce4e5b9ULL;
    value ^= value >> 27;
    value *= 0x94d049bb133111ebULL;
    value ^= value >> 31;
    return value;
}

std::uint64_t hash_hyperplane(const Hyperplane& hyperplane) {
    std::uint64_t hash = 0x243f6a8885a308d3ULL;
    for (std::size_t index = 0; index < hyperplane.size(); ++index) {
        hash ^= mix64(static_cast<std::uint64_t>(hyperplane[index]) +
                      0x9e3779b97f4a7c15ULL * (index + 1));
        hash = std::rotl(hash, 17);
        hash *= 0x9ddfea08eb382d69ULL;
    }
    return mix64(hash);
}

Hyperplane hyperplane_for_ref(const std::vector<State>& states,
                              const std::array<std::array<std::uint8_t, 4>, kNormals>& forms,
                              std::uint32_t ref) {
    const std::uint32_t state_index = ref / kNormals;
    const std::uint32_t normal_index = ref % kNormals;
    if (state_index >= states.size()) {
        throw std::runtime_error("hyperplane reference is out of range");
    }
    return canonical_hyperplane(state_coordinates(states[state_index]), forms[normal_index]);
}

std::vector<HashRef> enumerate_hyperplanes(
    const std::vector<State>& states,
    const std::array<std::array<std::uint8_t, 4>, kNormals>& forms,
    const char* label) {
    if (states.size() > UINT32_MAX / kNormals) {
        throw std::runtime_error("frontier is too large for 32-bit references");
    }
    std::vector<HashRef> records;
    records.reserve(states.size() * kNormals);
    const auto started = std::chrono::steady_clock::now();
    for (std::uint32_t state_index = 0; state_index < states.size(); ++state_index) {
        const auto coordinates = state_coordinates(states[state_index]);
        for (std::uint32_t normal_index = 0; normal_index < kNormals; ++normal_index) {
            const auto hyperplane = canonical_hyperplane(coordinates, forms[normal_index]);
            records.push_back({hash_hyperplane(hyperplane), state_index * kNormals + normal_index});
        }
        if ((state_index + 1) % 100000 == 0) {
            const auto seconds = std::chrono::duration<double>(
                std::chrono::steady_clock::now() - started).count();
            std::cerr << label << " generated " << (state_index + 1) << "/" << states.size()
                      << " states in " << seconds << " s\n";
        }
    }
    return records;
}

Basis basis_for_hyperplane(const Hyperplane& hyperplane) {
    Basis basis;
    for (const auto row : hyperplane) {
        basis.insert(row);
    }
    if (basis.rank != 5 || !basis.contains(kConstant)) {
        throw std::runtime_error("invalid shared hyperplane");
    }
    return basis;
}

Coordinates hyperplane_linear_coordinates(const Hyperplane& hyperplane) {
    Basis basis;
    basis.insert(kConstant);
    Coordinates result{};
    std::size_t count = 0;
    for (const auto row : hyperplane) {
        if (basis.insert(row)) {
            result[count++] = row;
        }
    }
    if (count != 4) {
        throw std::runtime_error("shared hyperplane does not have four linear coordinates");
    }
    return result;
}

std::uint32_t outside_row(const State& state, const Basis& hyperplane_basis) {
    for (const auto row : state) {
        if (!hyperplane_basis.contains(row)) {
            return row;
        }
    }
    throw std::runtime_error("state is contained in a rank-five hyperplane");
}

struct AdjacencyWitness {
    std::uint8_t left = 0;
    std::uint8_t right = 0;
    std::uint8_t left_constant = 0;
    std::uint8_t right_constant = 0;
    std::uint32_t source_outside = 0;
    std::uint32_t target_outside = 0;
};

bool adjacent(const State& source, const State& target, const Hyperplane& hyperplane,
              AdjacencyWitness& witness) {
    const auto hyperplane_basis = basis_for_hyperplane(hyperplane);
    const auto source_outside = outside_row(source, hyperplane_basis);
    const auto target_outside = outside_row(target, hyperplane_basis);
    const auto delta = source_outside ^ target_outside;
    const auto coordinates = hyperplane_linear_coordinates(hyperplane);

    std::array<std::uint32_t, 16> linear{};
    for (std::uint32_t form = 1; form < linear.size(); ++form) {
        for (std::size_t index = 0; index < 4; ++index) {
            if (((form >> index) & 1U) != 0) {
                linear[form] ^= coordinates[index];
            }
        }
    }
    for (std::uint32_t left = 1; left < 16; ++left) {
        for (std::uint32_t right = left + 1; right < 16; ++right) {
            for (std::uint32_t left_constant = 0; left_constant < 2; ++left_constant) {
                const auto left_mask = linear[left] ^ (left_constant ? kConstant : 0U);
                for (std::uint32_t right_constant = 0; right_constant < 2; ++right_constant) {
                    const auto right_mask = linear[right] ^ (right_constant ? kConstant : 0U);
                    const auto residual = delta ^ (left_mask & right_mask);
                    if (hyperplane_basis.contains(residual)) {
                        witness.left = static_cast<std::uint8_t>(left);
                        witness.right = static_cast<std::uint8_t>(right);
                        witness.left_constant = static_cast<std::uint8_t>(left_constant);
                        witness.right_constant = static_cast<std::uint8_t>(right_constant);
                        witness.source_outside = source_outside;
                        witness.target_outside = target_outside;
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

void print_words(const char* name, const auto& words) {
    std::cout << '\"' << name << "\":[";
    for (std::size_t index = 0; index < words.size(); ++index) {
        if (index != 0) {
            std::cout << ',';
        }
        std::cout << words[index];
    }
    std::cout << ']';
}

}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc != 3) {
            std::cerr << "usage: hyperplane_mitm X_DEPTH2.bin Y_DEPTH2.bin\n";
            return 2;
        }
        const auto started = std::chrono::steady_clock::now();
        const auto x_states = read_states(argv[1]);
        const auto y_states = read_states(argv[2]);
        const auto forms = invariant_bases();
        std::cerr << "loaded x=" << x_states.size() << " y=" << y_states.size() << " states\n";

        auto x_records = enumerate_hyperplanes(x_states, forms, "x");
        auto y_records = enumerate_hyperplanes(y_states, forms, "y");
        const auto by_hash = [](const HashRef& left, const HashRef& right) {
            return left.hash < right.hash;
        };
        std::cerr << "sorting x records=" << x_records.size() << "\n";
        std::sort(x_records.begin(), x_records.end(), by_hash);
        std::cerr << "sorting y records=" << y_records.size() << "\n";
        std::sort(y_records.begin(), y_records.end(), by_hash);

        std::size_t xi = 0;
        std::size_t yi = 0;
        std::uint64_t common_hashes = 0;
        std::uint64_t exact_hyperplane_pairs = 0;
        std::uint64_t tested_pairs = 0;
        std::uint32_t first_x_ref = UINT32_MAX;
        std::uint32_t first_y_ref = UINT32_MAX;
        Hyperplane first_shared_hyperplane{};
        while (xi < x_records.size() && yi < y_records.size()) {
            if (x_records[xi].hash < y_records[yi].hash) {
                ++xi;
                continue;
            }
            if (y_records[yi].hash < x_records[xi].hash) {
                ++yi;
                continue;
            }
            const auto hash = x_records[xi].hash;
            const auto x_begin = xi;
            const auto y_begin = yi;
            while (xi < x_records.size() && x_records[xi].hash == hash) {
                ++xi;
            }
            while (yi < y_records.size() && y_records[yi].hash == hash) {
                ++yi;
            }
            ++common_hashes;
            for (std::size_t x_index = x_begin; x_index < xi; ++x_index) {
                const auto x_ref = x_records[x_index].ref;
                const auto x_hyperplane = hyperplane_for_ref(x_states, forms, x_ref);
                for (std::size_t y_index = y_begin; y_index < yi; ++y_index) {
                    const auto y_ref = y_records[y_index].ref;
                    const auto y_hyperplane = hyperplane_for_ref(y_states, forms, y_ref);
                    if (x_hyperplane != y_hyperplane) {
                        continue;
                    }
                    ++exact_hyperplane_pairs;
                    if (first_x_ref == UINT32_MAX) {
                        first_x_ref = x_ref;
                        first_y_ref = y_ref;
                        first_shared_hyperplane = x_hyperplane;
                    }
                    AdjacencyWitness witness;
                    ++tested_pairs;
                    const auto& x_state = x_states[x_ref / kNormals];
                    const auto& y_state = y_states[y_ref / kNormals];
                    if (!adjacent(x_state, y_state, x_hyperplane, witness)) {
                        continue;
                    }
                    const auto seconds = std::chrono::duration<double>(
                        std::chrono::steady_clock::now() - started).count();
                    std::cout << '{';
                    std::cout << "\"verdict\":\"sat\",\"x_ref\":" << x_ref
                              << ",\"y_ref\":" << y_ref
                              << ",\"x_state_index\":" << x_ref / kNormals
                              << ",\"y_state_index\":" << y_ref / kNormals << ',';
                    print_words("x_state", x_state);
                    std::cout << ',';
                    print_words("y_state", y_state);
                    std::cout << ',';
                    print_words("shared_hyperplane", x_hyperplane);
                    std::cout << ",\"left\":" << static_cast<unsigned>(witness.left)
                              << ",\"right\":" << static_cast<unsigned>(witness.right)
                              << ",\"left_constant\":" << static_cast<unsigned>(witness.left_constant)
                              << ",\"right_constant\":" << static_cast<unsigned>(witness.right_constant)
                              << ",\"source_outside\":" << witness.source_outside
                              << ",\"target_outside\":" << witness.target_outside
                              << ",\"common_hashes\":" << common_hashes
                              << ",\"exact_hyperplane_pairs\":" << exact_hyperplane_pairs
                              << ",\"tested_pairs\":" << tested_pairs
                              << ",\"wall_seconds\":" << seconds << "}\n";
                    return 0;
                }
            }
        }
        const auto seconds = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - started).count();
        std::cout << "{\"verdict\":\"unsat\",\"common_hashes\":" << common_hashes
                  << ",\"exact_hyperplane_pairs\":" << exact_hyperplane_pairs
                  << ",\"tested_pairs\":" << tested_pairs;
        if (first_x_ref != UINT32_MAX) {
            std::cout << ",\"first_x_ref\":" << first_x_ref
                      << ",\"first_y_ref\":" << first_y_ref
                      << ",\"first_x_state_index\":" << first_x_ref / kNormals
                      << ",\"first_y_state_index\":" << first_y_ref / kNormals << ',';
            print_words("first_x_state", x_states[first_x_ref / kNormals]);
            std::cout << ',';
            print_words("first_y_state", y_states[first_y_ref / kNormals]);
            std::cout << ',';
            print_words("first_shared_hyperplane", first_shared_hyperplane);
        }
        std::cout << ",\"wall_seconds\":" << seconds << "}\n";
        return 1;
    } catch (const std::exception& error) {
        std::cerr << "error: " << error.what() << '\n';
        return 2;
    }
}
