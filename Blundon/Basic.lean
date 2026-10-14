import Mathlib

/-!
# Blundon's inequalities

For a triangle with circumradius `R`, inradius `r` and semiperimeter `s`,
`2R² + 10Rr − r² − 2(R − 2r)√(R² − 2Rr) ≤ s² ≤ 2R² + 10Rr − r² + 2(R − 2r)√(R² − 2Rr)`.

* `Blundon.blundon_core`: the algebraic statement in `(R, r, s)`, from the two defining relations
  `r²s = xyz` and `4Rrs = (y+z)(z+x)(x+y)` (`x, y, z` the tangent lengths `s - a`, `s - b`, `s - c`).
  The proof is a polynomial certificate: `s³(4r²E + Δ²) = 0` where
  `E = s⁴ − 2(2R² + 10Rr − r²)s² + r(4R + r)³` and `Δ = (a − b)(b − c)(c − a)`.
* `Blundon.blundon`: the inequality for an actual `Affine.Triangle ℝ P` (any real inner product
  space), with `R = t.circumradius`, `r = t.inradius` and `s` the semiperimeter from `dist`.
-/

open EuclideanGeometry RealInnerProductSpace

namespace Blundon

/-- The polynomial certificate behind Blundon's inequalities (`s = x + y + z`). -/
theorem core_identity {r R x y z : ℝ} (h1 : r ^ 2 * (x + y + z) = x * y * z)
    (h2 : 4 * R * r * (x + y + z) = (y + z) * (z + x) * (x + y)) :
    (x + y + z) ^ 3 * (4 * r ^ 2 * ((x + y + z) ^ 4 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) *
      (x + y + z) ^ 2 + r * (4 * R + r) ^ 3) + ((y - x) * (z - y) * (x - z)) ^ 2) = 0 := by
  linear_combination (64*R^2*r^2*x^2 + 128*R^2*r^2*x*y + 128*R^2*r^2*x*z + 64*R^2*r^2*y^2 + 128*R^2*r^2*y*z + 64*R^2*r^2*z^2 + 48*R*r^3*x^2 + 96*R*r^3*x*y + 96*R*r^3*x*z + 48*R*r^3*y^2 + 96*R*r^3*y*z + 48*R*r^3*z^2 - 4*R*r*x^4 + 8*R*r*x^2*y^2 + 16*R*r*x^2*y*z + 8*R*r*x^2*z^2 + 16*R*r*x*y^2*z + 16*R*r*x*y*z^2 - 4*R*r*y^4 + 8*R*r*y^2*z^2 - 4*R*r*z^4 + 12*r^4*x^2 + 24*r^4*x*y + 24*r^4*x*z + 12*r^4*y^2 + 24*r^4*y*z + 12*r^4*z^2 - 20*r^2*x^4 - 68*r^2*x^3*y - 68*r^2*x^3*z - 96*r^2*x^2*y^2 - 192*r^2*x^2*y*z - 96*r^2*x^2*z^2 - 68*r^2*x*y^3 - 192*r^2*x*y^2*z - 192*r^2*x*y*z^2 - 68*r^2*x*z^3 - 20*r^2*y^4 - 68*r^2*y^3*z - 96*r^2*y^2*z^2 - 68*r^2*y*z^3 - 20*r^2*z^4 - x^5*y - x^5*z + 2*x^3*y^3 + 5*x^3*y^2*z + 5*x^3*y*z^2 + 2*x^3*z^3 + 5*x^2*y^3*z + 10*x^2*y^2*z^2 + 5*x^2*y*z^3 - x*y^5 + 5*x*y^3*z^2 + 5*x*y^2*z^3 - x*z^5 - y^5*z + 2*y^3*z^3 - y*z^5) * h2 + (4*r^4*x^2 + 8*r^4*x*y + 8*r^4*x*z + 4*r^4*y^2 + 8*r^4*y*z + 4*r^4*z^2 + 8*r^2*x^4 + 44*r^2*x^3*y + 44*r^2*x^3*z + 72*r^2*x^2*y^2 + 148*r^2*x^2*y*z + 72*r^2*x^2*z^2 + 44*r^2*x*y^3 + 148*r^2*x*y^2*z + 148*r^2*x*y*z^2 + 44*r^2*x*z^3 + 8*r^2*y^4 + 44*r^2*y^3*z + 72*r^2*y^2*z^2 + 44*r^2*y*z^3 + 8*r^2*z^4 + 4*x^6 + 4*x^5*y + 4*x^5*z - 8*x^4*y^2 - 8*x^4*y*z - 8*x^4*z^2 - 16*x^3*y^3 - 32*x^3*y^2*z - 32*x^3*y*z^2 - 16*x^3*z^3 - 8*x^2*y^4 - 32*x^2*y^3*z - 44*x^2*y^2*z^2 - 32*x^2*y*z^3 - 8*x^2*z^4 + 4*x*y^5 - 8*x*y^4*z - 32*x*y^3*z^2 - 32*x*y^2*z^3 - 8*x*y*z^4 + 4*x*z^5 + 4*y^6 + 4*y^5*z - 8*y^4*z^2 - 16*y^3*z^3 - 8*y^2*z^4 + 4*y*z^5 + 4*z^6) * h1

/-- The algebraic core of Blundon's inequalities. -/
theorem blundon_core {r R s x y z : ℝ} (hr : 0 < r) (hR : 0 < R) (hs0 : 0 < s)
    (hs : s = x + y + z) (h1 : r ^ 2 * s = x * y * z)
    (h2 : 4 * R * r * s = (y + z) * (z + x) * (x + y)) :
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2 ∧
      s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) := by
  subst hs
  have key := core_identity h1 h2
  generalize x + y + z = s at key hs0
  have hE : s ^ 4 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) * s ^ 2 + r * (4 * R + r) ^ 3 ≤ 0 := by
    have h4 := (mul_eq_zero.1 key).resolve_left (pow_pos hs0 3).ne'
    by_contra hneg
    push Not at hneg
    have : 0 < 4 * r ^ 2 * (s ^ 4 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) * s ^ 2 +
        r * (4 * R + r) ^ 3) := by positivity
    nlinarith [sq_nonneg ((y - x) * (z - y) * (x - z))]
  have hsq : (s ^ 2 - (2 * R ^ 2 + 10 * R * r - r ^ 2)) ^ 2 ≤ 4 * R * (R - 2 * r) ^ 3 := by
    have : (s ^ 2 - (2 * R ^ 2 + 10 * R * r - r ^ 2)) ^ 2 - 4 * R * (R - 2 * r) ^ 3 =
        s ^ 4 - 2 * (2 * R ^ 2 + 10 * R * r - r ^ 2) * s ^ 2 + r * (4 * R + r) ^ 3 := by ring
    linarith
  have heuler : 0 ≤ R - 2 * r := by
    by_contra hneg
    push Not at hneg
    have h3 : (R - 2 * r) ^ 3 < 0 := Odd.pow_neg (by decide) hneg
    nlinarith [sq_nonneg (s ^ 2 - (2 * R ^ 2 + 10 * R * r - r ^ 2)), mul_pos hR (neg_pos.2 h3)]
  have hrad : 0 ≤ R ^ 2 - 2 * R * r := by nlinarith [mul_nonneg hR.le heuler]
  have hT := Real.sq_sqrt hrad
  have hT0 := Real.sqrt_nonneg (R ^ 2 - 2 * R * r)
  have hB : 0 ≤ 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) := by positivity
  have hsq' : (s ^ 2 - (2 * R ^ 2 + 10 * R * r - r ^ 2)) ^ 2 ≤
      (2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)) ^ 2 := by
    have : (2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)) ^ 2 = 4 * R * (R - 2 * r) ^ 3 := by
      rw [mul_pow, hT]; ring
    rw [this]; exact hsq
  have := abs_le_of_sq_le_sq' hsq' hB
  constructor <;> linarith [this.1, this.2]

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Four times the squared area of a triangle with sides `a, b, c` (Heron), i.e. the Gram
determinant of two edge vectors. -/
noncomputable def gram (a b c : ℝ) : ℝ :=
  (2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4) / 4

/-- The semiperimeter of a triangle. -/
noncomputable def semiperimeter (t : Affine.Triangle ℝ P) : ℝ :=
  (dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2) +
    dist (t.points 2) (t.points 0)) / 2

/-- Bridge for heights: `h_i² · (opposite side)² = gram`. -/
theorem height_sq_mul (t : Affine.Triangle ℝ P) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    t.height i ^ 2 * dist (t.points j) (t.points k) ^ 2 =
      gram (dist (t.points i) (t.points j)) (dist (t.points i) (t.points k))
        (dist (t.points j) (t.points k)) := by
  have hc : ({i}ᶜ : Set (Fin 3)) = {j, k} := by ext l; simp; omega
  have hF : t.altitudeFoot i ∈ line[ℝ, t.points j, t.points k] := by
    have := t.altitudeFoot_mem_affineSpan_image_compl i
    rwa [hc, Set.image_insert_eq, Set.image_singleton] at this
  obtain ⟨τ, hτ⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.1 hF
  have e1 := t.inner_vsub_vsub_altitudeFoot_eq_height_sq hij
  have e2 := t.inner_vsub_vsub_altitudeFoot_eq_height_sq hik
  set p := t.points i -ᵥ t.points j
  set q := t.points i -ᵥ t.points k
  have hw : t.points i -ᵥ t.altitudeFoot i = p - τ • (p - q) := by
    rw [← hτ, AffineMap.lineMap_apply, vsub_vadd_eq_vsub_sub]
    simp only [p, q, vsub_sub_vsub_cancel_left]
  rw [hw] at e1 e2
  simp only [inner_sub_right, inner_smul_right, real_inner_comm p q] at e1 e2
  have hP : ⟪p, p⟫ = dist (t.points i) (t.points j) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm_vsub V]
  have hQ : ⟪q, q⟫ = dist (t.points i) (t.points k) ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm_vsub V]
  have ha : dist (t.points j) (t.points k) ^ 2 = ⟪p, p⟫ - 2 * ⟪p, q⟫ + ⟪q, q⟫ := by
    rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_left (t.points j) (t.points k) (t.points i)]
    rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm]
    ring
  have hM : ⟪p, q⟫ = (dist (t.points i) (t.points j) ^ 2 + dist (t.points i) (t.points k) ^ 2
      - dist (t.points j) (t.points k) ^ 2) / 2 := by
    rw [ha, hP, hQ]; ring
  have core : t.height i ^ 2 * (⟪p, p⟫ - 2 * ⟪p, q⟫ + ⟪q, q⟫) = ⟪p, p⟫ * ⟪q, q⟫ - ⟪p, q⟫ ^ 2 := by
    linear_combination (⟪p, q⟫ - ⟪q, q⟫) * e1 + (⟪p, q⟫ - ⟪p, p⟫) * e2
  rw [ha, core, hM, hP, hQ, gram]
  ring

/-- Bridge for the circumradius: `4R² · gram = a²b²c²` (law of sines). -/
theorem circumradius_sq_mul (t : Affine.Triangle ℝ P) :
    4 * t.circumradius ^ 2 * gram (dist (t.points 0) (t.points 1)) (dist (t.points 1) (t.points 2))
      (dist (t.points 0) (t.points 2)) =
      dist (t.points 0) (t.points 1) ^ 2 * dist (t.points 1) (t.points 2) ^ 2 *
        dist (t.points 0) (t.points 2) ^ 2 := by
  have hls := t.dist_div_sin_angle_eq_two_mul_circumradius (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide)
  have hR := t.circumradius_pos
  have hc : 0 < dist (t.points 0) (t.points 1) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  have ha : 0 < dist (t.points 1) (t.points 2) :=
    dist_pos.2 (t.independent.injective.ne (by decide))
  set B := ∠ (t.points 0) (t.points 1) (t.points 2)
  have hsin : Real.sin B ≠ 0 := by
    intro h0; rw [h0, div_zero] at hls; linarith
  have hb : dist (t.points 0) (t.points 2) = 2 * t.circumradius * Real.sin B := by
    field_simp at hls; linarith
  have hlaw := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (t.points 0) (t.points 1) (t.points 2)
  rw [dist_comm (t.points 2) (t.points 1)] at hlaw
  have hpy := Real.sin_sq_add_cos_sq B
  set a := dist (t.points 1) (t.points 2)
  set b := dist (t.points 0) (t.points 2)
  set c := dist (t.points 0) (t.points 1)
  have hg : gram c a b = c ^ 2 * a ^ 2 * Real.sin B ^ 2 := by
    unfold gram
    linear_combination (-(c ^ 2 * a ^ 2)) * hpy +
      (c * a * Real.cos B - (b * b - (c * c + a * a - 2 * c * a * Real.cos B)) / 4) * hlaw
  rw [hg, hb]
  ring

/-- **Blundon's inequalities** for a triangle in a real inner product space. -/
theorem blundon (t : Affine.Triangle ℝ P) :
    2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 -
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) ≤
      semiperimeter t ^ 2 ∧
    semiperimeter t ^ 2 ≤
      2 * t.circumradius ^ 2 + 10 * t.circumradius * t.inradius - t.inradius ^ 2 +
        2 * (t.circumradius - 2 * t.inradius) *
          Real.sqrt (t.circumradius ^ 2 - 2 * t.circumradius * t.inradius) := by
  -- side lengths `a = BC`, `b = CA`, `c = AB`
  set a := dist (t.points 1) (t.points 2) with ha_def
  set b := dist (t.points 0) (t.points 2) with hb_def
  set c := dist (t.points 0) (t.points 1) with hc_def
  have ha : 0 < a := dist_pos.2 (t.independent.injective.ne (by decide))
  have hb : 0 < b := dist_pos.2 (t.independent.injective.ne (by decide))
  have hc : 0 < c := dist_pos.2 (t.independent.injective.ne (by decide))
  set G := gram c a b with hG
  have e0 := height_sq_mul t (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
  have e1 := height_sq_mul t (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide)
  have e2 := height_sq_mul t (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
  rw [dist_comm (t.points 1) (t.points 0)] at e1
  rw [dist_comm (t.points 2) (t.points 0), dist_comm (t.points 2) (t.points 1)] at e2
  rw [← ha_def, ← hb_def, ← hc_def] at e0 e1 e2
  replace e0 : (t.height 0 * a) ^ 2 = G := by rw [hG, mul_pow, e0] <;> unfold gram <;> ring
  replace e1 : (t.height 1 * b) ^ 2 = G := by rw [hG, mul_pow, e1] <;> unfold gram <;> ring
  replace e2 : (t.height 2 * c) ^ 2 = G := by rw [hG, mul_pow, e2] <;> unfold gram <;> ring
  have hh0 := t.height_pos 0
  have hh1 := t.height_pos 1
  have hh2 := t.height_pos 2
  have hG0 : 0 ≤ G := by rw [← e0]; positivity
  set g := Real.sqrt G with hg
  have hgG : g ^ 2 = G := Real.sq_sqrt hG0
  have hg0 : 0 < g := by
    rw [hg, ← e0, Real.sqrt_sq (by positivity)]; positivity
  have f0 : t.height 0 * a = g := by rw [hg, ← e0, Real.sqrt_sq (by positivity)]
  have f1 : t.height 1 * b = g := by rw [hg, ← e1, Real.sqrt_sq (by positivity)]
  have f2 : t.height 2 * c = g := by rw [hg, ← e2, Real.sqrt_sq (by positivity)]
  -- the inradius
  have w0 : (t.height 0)⁻¹ = a / g := by rw [← f0]; field_simp
  have w1 : (t.height 1)⁻¹ = b / g := by rw [← f1]; field_simp
  have w2 : (t.height 2)⁻¹ = c / g := by rw [← f2]; field_simp
  have hsum : ∑ i, t.excenterWeightsUnnorm ∅ i = (a + b + c) / g := by
    simp only [Affine.Simplex.excenterWeightsUnnorm, Finset.notMem_empty, if_false, one_mul]
    rw [Fin.sum_univ_three, w0, w1, w2]
    ring
  have hr : t.inradius = g / (a + b + c) := by
    rw [Affine.Simplex.inradius_eq_abs_inv_sum, hsum, inv_div, abs_of_pos (by positivity)]
  have hsp : semiperimeter t = (a + b + c) / 2 := by
    simp only [semiperimeter, dist_comm (t.points 2) (t.points 0), ← ha_def, ← hb_def, ← hc_def]
    ring
  have hRr := circumradius_sq_mul t
  rw [← ha_def, ← hb_def, ← hc_def, ← hG] at hRr
  have hR := t.circumradius_pos
  set R := t.circumradius
  set r := t.inradius
  set s := semiperimeter t
  have hr0 : 0 < r := by rw [hr]; positivity
  have hs0 : 0 < s := by rw [hsp]; positivity
  have hrs : r * (2 * s) = g := by rw [hr, hsp]; field_simp
  have hheron : G = 4 * s * (s - a) * (s - b) * (s - c) := by
    rw [hG, hsp] <;> unfold gram <;> ring
  refine blundon_core (x := s - a) (y := s - b) (z := s - c) hr0 hR hs0 (by rw [hsp]; ring) ?_ ?_
  · have h4 : 0 < 4 * s := by positivity
    have : 4 * s * (r ^ 2 * s) = 4 * s * ((s - a) * (s - b) * (s - c)) := by
      linear_combination (r * (2 * s) + g) * hrs + hgG + hheron
    exact mul_left_cancel₀ h4.ne' this
  · have hy : s - b + (s - c) = a := by rw [hsp]; ring
    have hz : s - c + (s - a) = b := by rw [hsp]; ring
    have hx : s - a + (s - b) = c := by rw [hsp]; ring
    rw [hy, hz, hx]
    have hsq : (4 * R * r * s) ^ 2 = (a * b * c) ^ 2 := by
      linear_combination (4 * R ^ 2) * ((r * (2 * s) + g) * hrs + hgG) + hRr
    have hu : 0 < 4 * R * r * s := by positivity
    have hv : 0 < a * b * c := by positivity
    have := mul_eq_zero.1 (show (4 * R * r * s - a * b * c) * (4 * R * r * s + a * b * c) = 0 by
      linear_combination hsq)
    rcases this with h | h
    · linarith
    · linarith

end Blundon
