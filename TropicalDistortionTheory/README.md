# Tropical Distortion Energy Theory

Rigorous Maslov dequantization of the von Mises distortion energy criterion.

## What's proven

Take the two classical formulas from Distortion Energy Theory:

- `u_d` — energy density under a general (triaxial) stress state
- `u_dy` — energy density at the point of yielding under simple tension

Reparametrize each physical quantity exponentially in a small parameter `ε`
(e.g. write `E = exp(Ẽ/ε)`), and ask what `ε · log(...)` of each formula
converges to as `ε → 0⁺`. This is the standard "Maslov dequantization" limit
that turns classical `+`/`×` into tropical `max`/`+` — done here as an actual
proved limit, not just a symbol-swap.

**Result:** both formulas dequantize to `(ν̃ - Ẽ) + [stress term]`, and the
`(ν̃ - Ẽ)` piece is identical on both sides — it cancels when you set
`u_d = u_dy` (the yield condition). What survives is:

```
max(σ̃₁, σ̃₂, σ̃₃) = σ̃_y
```

Informally: **yielding begins when the largest (log-scale) principal stress
reaches the yield stress.** That's the tropical/piecewise-linear counterpart
of the smooth von Mises criterion — structurally a max-stress criterion, in
the same family as Tresca's classical piecewise-linear approximation.

This equation just seemed relatively easy to tropicalize hence this small project
## Files

- `DistortionEnergy.lean` — classical definitions, the Maslov limit machinery,
  and the two main theorems (`dequant_u_d`, `dequant_u_dy`).