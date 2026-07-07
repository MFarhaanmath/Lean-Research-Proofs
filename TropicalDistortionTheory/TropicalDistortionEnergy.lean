/-
Copyright (c) 2026 Mohammed Farhaan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohammed Farhaan
-/
import Mathlib

/-!
# Maslov Dequantization of Distortion Energy Theory

Classical distortion energy equations, dequantized rigorously: reparametrize each positive
classical quantity `X` as `exp(x/ε)`, and show `ε · log(...)` genuinely converges as
`ε → 0⁺`. Core fact: `ε · log(exp(A/ε) + exp(B/ε)) → max A B` — the actual content of
"addition tropicalizes to max," proved as a limit, not asserted. Not in Mathlib
(`Mathlib.Algebra.Tropical.Basic` is purely algebraic — no `exp`/`log`/limit content), so
it's built from scratch below. Reference: G.L. Litvinov, arXiv:math/0501038.

`dequant_u_d` / `dequant_u_dy` at the bottom are the actual result: the rigorous
tropicalizations of the two classical equations.
-/

open Filter Topology
noncomputable section

def classical_u_d (ν E σ₁ σ₂ σ₃ : ℝ) : ℝ :=
  ((1 + ν) / (6 * E)) * ((σ₁ - σ₂) ^ 2 + (σ₂ - σ₃) ^ 2 + (σ₃ - σ₁) ^ 2)

def classical_u_dy (ν E σ_y : ℝ) : ℝ :=
  ((1 + ν) / (3 * E)) * σ_y ^ 2

-------------------------------------------------------------------------------
-- CORE MASLOV LIMIT MACHINERY
-------------------------------------------------------------------------------

theorem dequant_max (A B : ℝ) :
    Tendsto (fun ε : ℝ => ε * Real.log (Real.exp (A / ε) + Real.exp (B / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (max A B)) := by
  have key : ∀ ε : ℝ, 0 < ε →
      Real.exp (max A B / ε) = max (Real.exp (A / ε)) (Real.exp (B / ε)) := by
    intro ε hε
    rcases le_total A B with h | h
    · rw [max_eq_right h, max_eq_right (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hε).mpr h))]
    · rw [max_eq_left h, max_eq_left (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hε).mpr h))]
  have hlow : ∀ ε ∈ Set.Ioi (0 : ℝ), max A B ≤ ε * Real.log (Real.exp (A / ε) + Real.exp (B / ε)) := by
    intro ε hε
    have hle : Real.exp (max A B / ε) ≤ Real.exp (A / ε) + Real.exp (B / ε) := by
      rw [key ε hε]
      exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le)
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    have hεpos : (0 : ℝ) < ε := hε
    have hlog : max A B / ε ≤ Real.log (Real.exp (A / ε) + Real.exp (B / ε)) := by
      have := Real.log_le_log (Real.exp_pos (max A B / ε)) hle
      rwa [Real.log_exp] at this
    have h2 := mul_le_mul_of_nonneg_left hlog hεpos.le
    rwa [mul_div_cancel₀ _ hεpos.ne'] at h2
  have hhigh : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ε * Real.log (Real.exp (A / ε) + Real.exp (B / ε)) ≤ max A B + ε * Real.log 2 := by
    intro ε hε
    have hle : Real.exp (A / ε) + Real.exp (B / ε) ≤ 2 * Real.exp (max A B / ε) := by
      rw [key ε hε, two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
    have hlog : Real.log (Real.exp (A / ε) + Real.exp (B / ε)) ≤ Real.log 2 + max A B / ε := by
      have h1 := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
      linarith
    have h2 := mul_le_mul_of_nonneg_left hlog hε.le
    rw [mul_add, mul_div_cancel₀ _ hε.ne'] at h2
    linarith
  have hupper : Tendsto (fun ε : ℝ => max A B + ε * Real.log 2) (𝓝[>] (0 : ℝ)) (𝓝 (max A B)) := by
    have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using (h0.mul_const (Real.log 2)).const_add (max A B)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.eventually_of_mem self_mem_nhdsWithin hlow)
    (Filter.eventually_of_mem self_mem_nhdsWithin hhigh)

theorem dequant_max3 (A B C : ℝ) :
    Tendsto (fun ε : ℝ => ε * Real.log (Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (max A (max B C))) := by
  set M := max A (max B C) with hM
  have key : ∀ ε : ℝ, 0 < ε →
      Real.exp (M / ε) = max (Real.exp (A / ε)) (max (Real.exp (B / ε)) (Real.exp (C / ε))) := by
    intro ε hε
    have h1 : ∀ x y ε' : ℝ, 0 < ε' →
        Real.exp (max x y / ε') = max (Real.exp (x / ε')) (Real.exp (y / ε')) := by
      intro x y ε' hε'
      rcases le_total x y with h | h
      · rw [max_eq_right h, max_eq_right (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hε').mpr h))]
      · rw [max_eq_left h, max_eq_left (Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hε').mpr h))]
    rw [hM, h1 A (max B C) ε hε, h1 B C ε hε]
  have hlow : ∀ ε ∈ Set.Ioi (0 : ℝ),
      M ≤ ε * Real.log (Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε)) := by
    intro ε hε
    have hle : Real.exp (M / ε) ≤ Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε) := by
      rw [key ε hε]
      apply max_le
      · nlinarith [Real.exp_pos (B / ε), Real.exp_pos (C / ε)]
      · apply max_le <;> nlinarith [Real.exp_pos (A / ε), Real.exp_pos (B / ε), Real.exp_pos (C / ε)]
    have hεpos : (0 : ℝ) < ε := hε
    have hlog : M / ε ≤ Real.log (Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε)) := by
      have := Real.log_le_log (Real.exp_pos (M / ε)) hle
      rwa [Real.log_exp] at this
    have h2 := mul_le_mul_of_nonneg_left hlog hεpos.le
    rwa [mul_div_cancel₀ _ hεpos.ne'] at h2
  have hhigh : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ε * Real.log (Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε)) ≤ M + ε * Real.log 3 := by
    intro ε hε
    have key' := key ε hε
    have h1 : Real.exp (A / ε) ≤ Real.exp (M / ε) := key' ▸ le_max_left _ _
    have h2 : Real.exp (B / ε) ≤ Real.exp (M / ε) := key' ▸ le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : Real.exp (C / ε) ≤ Real.exp (M / ε) := key' ▸ le_trans (le_max_right _ _) (le_max_right _ _)
    have hle : Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε) ≤ 3 * Real.exp (M / ε) := by linarith
    have hlog : Real.log (Real.exp (A / ε) + Real.exp (B / ε) + Real.exp (C / ε)) ≤ Real.log 3 + M / ε := by
      have h4 := Real.log_le_log (by positivity) hle
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h4
      linarith
    have h5 := mul_le_mul_of_nonneg_left hlog hε.le
    rw [mul_add, mul_div_cancel₀ _ hε.ne'] at h5
    linarith
  have hupper : Tendsto (fun ε : ℝ => M + ε * Real.log 3) (𝓝[>] (0 : ℝ)) (𝓝 M) := by
    have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using (h0.mul_const (Real.log 3)).const_add M
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.eventually_of_mem self_mem_nhdsWithin hlow)
    (Filter.eventually_of_mem self_mem_nhdsWithin hhigh)

/-- Reparametrize `1+ν = exp(ν/ε)`, `E = exp(Et/ε)`. The prefactor `(1+ν)/(k·E)` dequantizes
    to `ν - Et`, exactly: `ε·log(...) = ν - Et - ε·log k`, so the bare constant `k` (6 or 3)
    vanishes in the limit rather than surviving as `-k`. -/
theorem dequant_prefactor (k : ℝ) (hk : 0 < k) (ν Et : ℝ) :
    Tendsto (fun ε : ℝ => ε * Real.log ((1 + (Real.exp (ν / ε) - 1)) / (k * Real.exp (Et / ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν - Et)) := by
  have heq : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ε * Real.log ((1 + (Real.exp (ν / ε) - 1)) / (k * Real.exp (Et / ε))) = ν - Et - ε * Real.log k := by
    intro ε hε
    have hεpos : (0 : ℝ) < ε := hε
    have h1 : (1 + (Real.exp (ν / ε) - 1)) = Real.exp (ν / ε) := by ring
    rw [h1, Real.log_div (Real.exp_pos _).ne' (by positivity),
        Real.log_mul hk.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    field_simp
    ring
  have htendsto : Tendsto (fun ε : ℝ => ν - Et - ε * Real.log k) (𝓝[>] (0 : ℝ)) (𝓝 (ν - Et)) := by
    have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using (tendsto_const_nhds (x := ν - Et)).sub (h0.mul_const (Real.log k))
  exact htendsto.congr' (Filter.eventually_of_mem self_mem_nhdsWithin (fun ε hε => (heq ε hε).symm))

/-- For `σ₁ ≠ σ₂`, eventually (small `ε`) the squared difference of the exponentially
    reparametrized stresses sits between `(1/4)exp(2max/ε)` and `exp(2max/ε)` — the sandwich
    that makes `(σ₁-σ₂)² ↦ 2max(σ₁,σ₂)` a genuine limit rather than a sign-blind rewrite. -/
theorem sq_diff_bounds (p q : ℝ) (hpq : p ≠ q) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (1 / 4) * Real.exp (2 * max p q / ε) ≤ (Real.exp (p / ε) - Real.exp (q / ε)) ^ 2 ∧
      (Real.exp (p / ε) - Real.exp (q / ε)) ^ 2 ≤ Real.exp (2 * max p q / ε) := by
  wlog hlt : q < p generalizing p q with H
  · have := H q p hpq.symm ((lt_or_gt_of_ne hpq).resolve_right hlt)
    simpa [max_comm, show ∀ x y : ℝ, (x - y) ^ 2 = (y - x) ^ 2 from fun x y => by ring] using this
  set δ := p - q with hδ
  have hδpos : 0 < δ := by simp [hδ]; linarith
  set ε₀ := δ / Real.log 2 with hε₀
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hε₀pos : 0 < ε₀ := div_pos hδpos hlog2pos
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ε₀ :=
    Filter.eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hε₀pos)) (fun ε hε => hε)
  filter_upwards [self_mem_nhdsWithin, hev] with ε hεpos hεlt
  have hstep2 : Real.log 2 < δ / ε := by
    rw [lt_div_iff₀ hεpos]; rw [lt_div_iff₀ hlog2pos] at hεlt; nlinarith [hεlt]
  have hexp_le : Real.exp ((q - p) / ε) ≤ 1 / 2 := by
    have hqp : (q - p) / ε = -(δ / ε) := by rw [hδ]; ring
    rw [hqp]
    calc Real.exp (-(δ / ε)) ≤ Real.exp (-(Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hexp_lt1 : Real.exp ((q - p) / ε) < 1 := by
    have hneg : (q - p) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hεpos
    calc Real.exp ((q - p) / ε) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hfactor : Real.exp (p / ε) - Real.exp (q / ε) = Real.exp (p / ε) * (1 - Real.exp ((q - p) / ε)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [max_eq_left hlt.le]
  constructor
  · have h2 : (1 / 2) * Real.exp (p / ε) ≤ Real.exp (p / ε) - Real.exp (q / ε) := by
      rw [hfactor]; nlinarith [Real.exp_pos (p / ε), hexp_le]
    have h6 := pow_le_pow_left₀ (by positivity) h2 2
    have h7 : ((1 : ℝ) / 2) ^ 2 * Real.exp (p / ε) ^ 2 = (1 / 4) * Real.exp (2 * p / ε) := by
      rw [show Real.exp (p / ε) ^ 2 = Real.exp (2 * p / ε) from by
        rw [pow_two, ← Real.exp_add]; congr 1; ring]
      ring
    rw [mul_pow] at h6; linarith [h6, h7]
  · have h2 : (0 : ℝ) ≤ Real.exp (p / ε) - Real.exp (q / ε) := by
      rw [hfactor]; nlinarith [Real.exp_pos (p / ε), hexp_lt1]
    have h1 : Real.exp (p / ε) - Real.exp (q / ε) ≤ Real.exp (p / ε) := by
      have := Real.exp_pos (q / ε); linarith
    have h4 := pow_le_pow_left₀ h2 h1 2
    have h5 : Real.exp (p / ε) ^ 2 = Real.exp (2 * p / ε) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    linarith [h4, h5]

private theorem sq_diff_pos (p q ε : ℝ) (hpq : p ≠ q) (hε : ε ≠ 0) :
    0 < (Real.exp (p / ε) - Real.exp (q / ε)) ^ 2 := by
  have hpqe : p / ε ≠ q / ε := by
    intro hcontra
    apply hpq
    have h1 : p / ε * ε = q / ε * ε := by rw [hcontra]
    rwa [div_mul_cancel₀ p hε, div_mul_cancel₀ q hε] at h1
  have hne : Real.exp (p / ε) ≠ Real.exp (q / ε) := by
    rcases lt_or_gt_of_ne hpqe with hlt | hlt
    · exact (Real.exp_lt_exp.mpr hlt).ne
    · exact (Real.exp_lt_exp.mpr hlt).ne'
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with h | h <;> nlinarith

-------------------------------------------------------------------------------
-- THE RESULT: rigorous tropicalization of `u_d` and `u_dy`
-------------------------------------------------------------------------------

/-- The genuine Maslov dequantization of `classical_u_dy`. -/
theorem dequant_u_dy (ν Et σ_y : ℝ) :
    Tendsto (fun ε : ℝ => ε * Real.log
        (classical_u_dy (Real.exp (ν / ε) - 1) (Real.exp (Et / ε)) (Real.exp (σ_y / ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν - Et + 2 * σ_y)) := by
  have heq : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ε * Real.log (classical_u_dy (Real.exp (ν / ε) - 1) (Real.exp (Et / ε)) (Real.exp (σ_y / ε)))
        = ε * Real.log ((1 + (Real.exp (ν / ε) - 1)) / (3 * Real.exp (Et / ε)))
          + ε * (2 * Real.log (Real.exp (σ_y / ε))) := by
    intro ε _
    unfold classical_u_dy
    have hnum : (1 : ℝ) + (Real.exp (ν / ε) - 1) = Real.exp (ν / ε) := by ring
    rw [hnum, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have h2 : Tendsto (fun ε : ℝ => ε * (2 * Real.log (Real.exp (σ_y / ε)))) (𝓝[>] (0 : ℝ)) (𝓝 (2 * σ_y)) := by
    have heq2 : ∀ ε ∈ Set.Ioi (0 : ℝ), ε * (2 * Real.log (Real.exp (σ_y / ε))) = 2 * σ_y := by
      intro ε hε; have hne : ε ≠ 0 := (hε : (0 : ℝ) < ε).ne'
      rw [Real.log_exp]; field_simp
    exact tendsto_const_nhds.congr'
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun ε hε => (heq2 ε hε).symm))
  exact ((dequant_prefactor 3 (by norm_num) ν Et).add h2).congr'
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun ε hε => (heq ε hε).symm))

/-- The genuine Maslov dequantization of `classical_u_d`, generically (pairwise distinct
    stress valuations, i.e. off the tropical variety of coinciding principal stresses). -/
theorem dequant_u_d (ν Et σ₁ σ₂ σ₃ : ℝ) (h12 : σ₁ ≠ σ₂) (h23 : σ₂ ≠ σ₃) (h31 : σ₃ ≠ σ₁) :
    Tendsto (fun ε : ℝ => ε * Real.log
        (classical_u_d (Real.exp (ν / ε) - 1) (Real.exp (Et / ε))
          (Real.exp (σ₁ / ε)) (Real.exp (σ₂ / ε)) (Real.exp (σ₃ / ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν - Et + 2 * max σ₁ (max σ₂ σ₃))) := by
  have hcollapse : max (2 * max σ₁ σ₂) (max (2 * max σ₂ σ₃) (2 * max σ₃ σ₁)) = 2 * max σ₁ (max σ₂ σ₃) := by
    rcases le_total σ₁ σ₂ with h12' | h12' <;> rcases le_total σ₂ σ₃ with h23' | h23' <;>
    rcases le_total σ₁ σ₃ with h13' | h13' <;> simp_all only [max_def] <;> split_ifs <;> linarith
  have hSlim := dequant_max3 (2 * max σ₁ σ₂) (2 * max σ₂ σ₃) (2 * max σ₃ σ₁)
  rw [hcollapse] at hSlim
  set S : ℝ → ℝ := fun ε => Real.exp (2 * max σ₁ σ₂ / ε) + Real.exp (2 * max σ₂ σ₃ / ε) + Real.exp (2 * max σ₃ σ₁ / ε)
  set br : ℝ → ℝ := fun ε => (Real.exp (σ₁ / ε) - Real.exp (σ₂ / ε)) ^ 2 + (Real.exp (σ₂ / ε) - Real.exp (σ₃ / ε)) ^ 2
    + (Real.exp (σ₃ / ε) - Real.exp (σ₁ / ε)) ^ 2
  have hb12 := sq_diff_bounds σ₁ σ₂ h12
  have hb23 := sq_diff_bounds σ₂ σ₃ h23
  have hb31 := sq_diff_bounds σ₃ σ₁ h31
  have hlowlim : Tendsto (fun ε => ε * Real.log ((1 / 4) * S ε)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * max σ₁ (max σ₂ σ₃))) := by
    have heq : ∀ ε ∈ Set.Ioi (0 : ℝ), ε * Real.log ((1 / 4) * S ε) = ε * Real.log (1 / 4) + ε * Real.log (S ε) := by
      intro ε _
      have hSpos : 0 < S ε := by simp only [S]; positivity
      rw [Real.log_mul (by norm_num) hSpos.ne']; ring
    have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hcomb := (h0.mul_const (Real.log (1 / 4))).add hSlim
    simp only [zero_mul, zero_add] at hcomb
    exact hcomb.congr' (Filter.eventually_of_mem self_mem_nhdsWithin (fun ε hε => (heq ε hε).symm))
  have hlowfun : (fun ε => ε * Real.log ((1 / 4) * S ε)) ≤ᶠ[𝓝[>] (0 : ℝ)] (fun ε => ε * Real.log (br ε)) := by
    filter_upwards [hb12, hb23, hb31, self_mem_nhdsWithin] with ε h12' h23' h31' hεpos
    have hε0 : (0 : ℝ) < ε := hεpos
    have hsum : (1 / 4) * S ε ≤ br ε := by simp only [S, br]; linarith [h12'.1, h23'.1, h31'.1]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by simp only [S]; positivity) hsum) hε0.le
  have hhighfun : (fun ε => ε * Real.log (br ε)) ≤ᶠ[𝓝[>] (0 : ℝ)] (fun ε => ε * Real.log (S ε)) := by
    filter_upwards [hb12, hb23, hb31, self_mem_nhdsWithin] with ε h12' h23' h31' hεpos
    have hε0 : (0 : ℝ) < ε := hεpos
    have hbrpos : 0 < br ε := by
      have := sq_diff_pos σ₁ σ₂ ε h12 hε0.ne'
      simp only [br]; nlinarith [sq_nonneg (Real.exp (σ₂ / ε) - Real.exp (σ₃ / ε)),
        sq_nonneg (Real.exp (σ₃ / ε) - Real.exp (σ₁ / ε))]
    have hsum : br ε ≤ S ε := by simp only [S, br]; linarith [h12'.2, h23'.2, h31'.2]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hbrpos hsum) hε0.le
  have hbrlim : Tendsto (fun ε => ε * Real.log (br ε)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * max σ₁ (max σ₂ σ₃))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowlim hSlim hlowfun hhighfun
  have heq : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ε * Real.log (classical_u_d (Real.exp (ν / ε) - 1) (Real.exp (Et / ε))
          (Real.exp (σ₁ / ε)) (Real.exp (σ₂ / ε)) (Real.exp (σ₃ / ε)))
        = ε * Real.log ((1 + (Real.exp (ν / ε) - 1)) / (6 * Real.exp (Et / ε))) + ε * Real.log (br ε) := by
    intro ε hε
    have hε0 : (0 : ℝ) < ε := hε
    unfold classical_u_d
    have hbrpos : 0 < br ε := by
      have := sq_diff_pos σ₁ σ₂ ε h12 hε0.ne'
      simp only [br]; nlinarith [sq_nonneg (Real.exp (σ₂ / ε) - Real.exp (σ₃ / ε)),
        sq_nonneg (Real.exp (σ₃ / ε) - Real.exp (σ₁ / ε))]
    have hnum : (1 + (Real.exp (ν / ε) - 1)) = Real.exp (ν / ε) := by ring
    rw [Real.log_mul (by rw [hnum]; positivity) hbrpos.ne']
    ring
  exact ((dequant_prefactor 6 (by norm_num) ν Et).add hbrlim).congr'
    (Filter.eventually_of_mem self_mem_nhdsWithin (fun ε hε => (heq ε hε).symm))

end
