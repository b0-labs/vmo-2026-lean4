# Formal Verification of Vietnamese Math Olympiad Problems in Lean 4

A collection of formally verified mathematical proofs using Lean 4 and Mathlib, demonstrating the power of AI-assisted theorem proving for competition mathematics.

---

## Overview

This repository contains Lean 4 formalizations of problems from the Vietnamese Mathematical Olympiad. Each proof has been:

- **Mathematically solved** with rigorous human-readable proofs
- **Formally verified** in Lean 4 with Mathlib
- **Machine-checked** for 100% correctness guarantee

---

## Verification Status

| Problem | Existence | Uniqueness/Bound | Main Theorem |
|---------|-----------|------------------|--------------|
| Problem 1a | ✅ | ✅ | ✅ `P_has_unique_pos_root` |
| Problem 1b | ✅ | ✅ | ✅ `c_converges` |
| Problem 3 | ✅ | ✅ | ✅ `divisors_in_interval_eq` |
| Problem 4a | ✅ | ✅ | ✅ `part_a` |
| Problem 4b | ✅ | ✅ | ✅ `part_b` |

---

## Mathematical Significance

These formalizations demonstrate:

1. **AI + Formal Methods Synergy**: AI assists in proof discovery while Lean guarantees correctness
2. **Competition Math Formalization**: Olympiad problems can be machine-verified
3. **Diverse Techniques**: Number theory, real analysis, and combinatorics unified in one framework
4. **Automation Power**: Modern tactics can handle substantial proof obligations

---

## License

MIT License — See [LICENSE](LICENSE) for details.

---

## Contributing

Contributions welcome! Areas of interest:

- Simplifying existing proofs
- Reducing automation reliance (replacing `grind` with explicit steps)
- Adding more olympiad problems
- Improving documentation

---

*"The computer does not understand mathematics. But it can verify that we do."*