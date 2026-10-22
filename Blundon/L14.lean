import Blundon.Basic

/-!
# Layer 14: Mathlib-only restatement and a witness for Blundon's inequalities

`l14_blundon` mentions only Mathlib notions: `Affine.Simplex.circumradius`, `Affine.Simplex.inradius`
and `dist`. The library's `semiperimeter` is written out as `(AB + BC + CA) / 2`.
`l14w_blundon` is the 3-4-5 triangle `0, 4, 3i` in `ℂ`. It is scalene (in particular not
equilateral), with `R = 5/2`, `r = 1`, `s = 6`, and both inequalities are strict:
`36.5 - √1.25 < 36 < 36.5 + √1.25`.
Equality cases: by `core_identity`, `s³(4r²E + Δ²) = 0` with `Δ = (a-b)(b-c)(c-a)`. So one of the
two bounds is attained exactly when `E = 0`, i.e. `Δ = 0`: the triangle is isosceles. Equilateral
triangles attain both, since `R = 2r` there.
-/

namespace Blundon

open EuclideanGeometry Complex

/-- **Blundon's inequalities**, Mathlib-only statement. -/
theorem l14_blundon {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) :
    2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 -
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) ≤
      ((dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
        dist (t.points 2) (t.points 0)) / 2) ^ 2 ∧
    ((dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
        dist (t.points 2) (t.points 0)) / 2) ^ 2 ≤
      2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 +
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) :=
  blundon t

/-! ### Bridges for the witness -/

theorem l14b_norm_eq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 = r ^ 2) : ‖z‖ = r := by
  rw [Complex.norm_def, Complex.normSq_apply, ← sq, ← sq, h, Real.sqrt_sq hr]

theorem l14b_not_collinear {a b c : ℂ}
    (h : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0) :
    ¬Collinear ℝ ({a, b, c} : Set ℂ) := by
  rw [collinear_iff_of_mem (p₀ := a) (by simp)]
  rintro ⟨v, hv⟩
  obtain ⟨s, hs⟩ := hv b (by simp)
  obtain ⟨t, ht⟩ := hv c (by simp)
  apply h
  rw [hs, ht]
  simp only [vadd_eq_add, add_sub_cancel_right, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The inradius from the heights (`r⁻¹ = ∑ hᵢ⁻¹`, Mathlib's `inradius_eq_abs_inv_sum`). -/
theorem l14b_inradius {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
    [NormedAddTorsor V P] (t : Affine.Triangle ℝ P) :
    t.inradius = ((t.height 0)⁻¹ + (t.height 1)⁻¹ + (t.height 2)⁻¹)⁻¹ := by
  have h0 := t.height_pos 0
  have h1 := t.height_pos 1
  have h2 := t.height_pos 2
  rw [Affine.Simplex.inradius_eq_abs_inv_sum]
  simp only [Affine.Simplex.excenterWeightsUnnorm, Finset.notMem_empty, if_false, one_mul]
  rw [Fin.sum_univ_three, abs_of_pos (by positivity)]

/-- Witness for `l14_blundon`: the 3-4-5 triangle, scalene, with `R = 5/2`, `r = 1`, `s = 6`,
and both inequalities strict. -/
theorem l14w_blundon :
    ∃ t : Affine.Triangle ℝ ℂ, t.points = ![0, 4, 3 * I] ∧
      dist (t.points 0) (t.points 1) = 4 ∧ dist (t.points 1) (t.points 2) = 5 ∧
      dist (t.points 2) (t.points 0) = 3 ∧
      t.circumradius = 5 / 2 ∧ t.inradius = 1 ∧
      (dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
        dist (t.points 2) (t.points 0)) / 2 = 6 ∧
      2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 -
          2 * (t.circumradius - 2 * t.inradius) *
            Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) <
        ((dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
          dist (t.points 2) (t.points 0)) / 2) ^ 2 ∧
      ((dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
          dist (t.points 2) (t.points 0)) / 2) ^ 2 <
        2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 +
          2 * (t.circumradius - 2 * t.inradius) *
            Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) := by
  have hnc : ¬Collinear ℝ ({(0 : ℂ), 4, 3 * I} : Set ℂ) := l14b_not_collinear (by norm_num)
  refine ⟨⟨![0, 4, 3 * I], affineIndependent_iff_not_collinear_set.2 hnc⟩, rfl, ?_⟩
  set t : Affine.Triangle ℝ ℂ := ⟨![0, 4, 3 * I], affineIndependent_iff_not_collinear_set.2 hnc⟩
  have p0 : t.points 0 = 0 := rfl
  have p1 : t.points 1 = 4 := rfl
  have p2 : t.points 2 = 3 * I := rfl
  have d01 : dist (t.points 0) (t.points 1) = 4 := by
    rw [p0, p1, Complex.dist_eq]; exact l14b_norm_eq (by norm_num) (by norm_num)
  have d12 : dist (t.points 1) (t.points 2) = 5 := by
    rw [p1, p2, Complex.dist_eq]; exact l14b_norm_eq (by norm_num) (by norm_num)
  have d20 : dist (t.points 2) (t.points 0) = 3 := by
    rw [p2, p0, Complex.dist_eq]; exact l14b_norm_eq (by norm_num) (by norm_num)
  have d02 : dist (t.points 0) (t.points 2) = 3 := by rw [dist_comm, d20]
  have d10 : dist (t.points 1) (t.points 0) = 4 := by rw [dist_comm, d01]
  have d21 : dist (t.points 2) (t.points 1) = 5 := by rw [dist_comm, d12]
  -- circumradius from the law-of-sines bridge
  have hRe := circumradius_sq_mul t
  rw [d01, d12, d02] at hRe
  have hR0 := t.circumradius_pos
  have hR : t.circumradius = 5 / 2 := by
    unfold gram at hRe
    have : (t.circumradius - 5 / 2) * (t.circumradius + 5 / 2) = 0 := by
      linear_combination hRe / 576
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  -- heights from the height bridge, then the inradius
  have e0 := height_sq_mul t (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
  have e1 := height_sq_mul t (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)
  have e2 := height_sq_mul t (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
  rw [d01, d02, d12] at e0
  rw [d10, d12, d02] at e1
  rw [d20, d21, d01] at e2
  unfold gram at e0 e1 e2
  have q0 := t.height_pos 0
  have q1 := t.height_pos 1
  have q2 := t.height_pos 2
  have g0 : t.height 0 = 12 / 5 := by
    have : (t.height 0 - 12 / 5) * (t.height 0 + 12 / 5) = 0 := by linear_combination e0 / 25
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have g1 : t.height 1 = 4 := by
    have : (t.height 1 - 4) * (t.height 1 + 4) = 0 := by linear_combination e1 / 9
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have g2 : t.height 2 = 3 := by
    have : (t.height 2 - 3) * (t.height 2 + 3) = 0 := by linear_combination e2 / 16
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hr : t.inradius = 1 := by rw [l14b_inradius, g0, g1, g2]; norm_num
  have h5 : (1 : ℝ) < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  refine ⟨d01, d12, d20, hR, hr, ?_, ?_, ?_⟩
  · rw [d01, d12, d20]; norm_num
  · rw [hR, hr, d01, d12, d20]; norm_num; linarith
  · rw [hR, hr, d01, d12, d20]; norm_num; linarith

end Blundon
