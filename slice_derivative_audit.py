import itertools
from fractions import Fraction
from typing import Callable, Dict, FrozenSet, List


def evaluate_exact_slice_calculus(
    universe: List[int],
    loss_fn: Callable[[FrozenSet[int]], Fraction],
    max_k: int = 3,
) -> Dict[str, object]:
    # Precompute exactly the states needed for A_0,...,A_max_k and
    # derivatives j=0,...,max_k-1.  For N=12,max_k=3 this is 299 states.
    loss_cache: Dict[FrozenSet[int], Fraction] = {}
    for r in range(max_k + 1):
        for s in itertools.combinations(universe, r):
            fs = frozenset(s)
            loss_cache[fs] = loss_fn(fs)

    A: Dict[int, Fraction] = {}
    for j in range(max_k + 1):
        slice_j = [frozenset(s) for s in itertools.combinations(universe, j)]
        A[j] = sum((loss_cache[s] for s in slice_j), Fraction(0, 1)) / Fraction(
            len(slice_j), 1
        )

    slice_diffs = []
    pair_avg_derivs = []
    residuals = []

    for j in range(max_k):
        slice_j = [frozenset(s) for s in itertools.combinations(universe, j)]
        slice_diff = A[j + 1] - A[j]

        total_deriv = Fraction(0, 1)
        pair_count = 0
        for S in slice_j:
            for v in universe:
                if v not in S:
                    total_deriv += loss_cache[S | {v}] - loss_cache[S]
                    pair_count += 1

        pair_avg = total_deriv / Fraction(pair_count, 1)
        residual = slice_diff - pair_avg

        slice_diffs.append(slice_diff)
        pair_avg_derivs.append(pair_avg)
        residuals.append(residual)

    telescoped_diff = A[max_k] - A[0]
    sum_derivatives = sum(pair_avg_derivs, Fraction(0, 1))
    global_residual = telescoped_diff - sum_derivatives

    return {
        "cached_states_count": len(loss_cache),
        "A": A,
        "slice_diffs": slice_diffs,
        "pair_avg_derivs": pair_avg_derivs,
        "residuals": residuals,
        "telescoped_diff": telescoped_diff,
        "sum_derivatives": sum_derivatives,
        "global_residual": global_residual,
        "all_exact_zeros": all(r == 0 for r in residuals) and global_residual == 0,
    }


if __name__ == "__main__":
    U = list(range(12))

    def exact_cavity_loss(S: FrozenSet[int]) -> Fraction:
        if not S:
            return Fraction(0, 1)
        base = sum((Fraction(1, 10000) * (x + 1) for x in S), Fraction(0, 1))
        interaction = sum(
            (
                Fraction(1, 50000) * ((x * y) % 7)
                for x, y in itertools.combinations(S, 2)
            ),
            Fraction(0, 1),
        )
        return base + interaction

    out = evaluate_exact_slice_calculus(U, exact_cavity_loss, max_k=3)

    assert out["cached_states_count"] == 299
    assert out["all_exact_zeros"] is True
    assert out["residuals"] == [Fraction(0, 1)] * 3
    assert out["global_residual"] == Fraction(0, 1)

    print(f"Total states cached: {out['cached_states_count']} (expected: 299)")
    print(f"A_0: {out['A'][0]}")
    print(f"A_1: {out['A'][1]}")
    print(f"A_2: {out['A'][2]}")
    print(f"A_3: {out['A'][3]}")
    print("Exact step residuals:", [str(r) for r in out["residuals"]])
    print("Exact global residual:", str(out["global_residual"]))
    print("V53 exact audit gate: CLOSED / ZERO_RESIDUAL")
