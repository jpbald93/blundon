import Blundon.Basic

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/


/-!
# Paper D — classical statements D1–D7 (blind formalisation)

All statements live in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`.
Constructed objects (second intersection points, Clifford points, Fermat points,
Thébault circles, auxiliary circumcentres, bisector feet) are passed in as data
together with their DEFINING property; well-definedness facts that are needed only
to make such data exist are stated separately as `_obligation` theorems.
-/

open EuclideanGeometry

noncomputable section

namespace Blundon.Classical

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ## D1 — Clifford's circle theorems -/

/-- OWN DEFINITION. General position hypothesis of D1 for `n` circles `c i` through a
common point `M`: genuine circles (positive radius), pairwise distinct, `P i j` is a
second common point of `c i` and `c j` different from `M`, and for any three circles the
three second points are not collinear. (Since distinct circles meet in at most two points,
`P i j` is uniquely determined by these conditions.) -/
structure CliffordGP (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt) (P : Fin n → Fin n → Pt) :
    Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  second_mem : ∀ i j, i ≠ j → P i j ∈ c i ∧ P i j ∈ c j
  second_ne : ∀ i j, i ≠ j → P i j ≠ M
  noncollinear : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i j, P i k, P j k}

/-- OWN DEFINITION. `X` lies on every circle `Γ_ijk` (through the non-collinear points
`P i j, P i k, P j k`) for `i, j, k` pairwise distinct in `S`. For `S` with four elements
this says that `X` is a common point of the four circles of D1(a) (a "Clifford point").
Because `P i j, P i k, P j k` are non-collinear, `Cospherical {P i j, P i k, P j k, X}`
means exactly that `X` lies on their (unique) circumcircle. -/
def OnAllGamma {n : ℕ} (P : Fin n → Fin n → Pt) (S : Finset (Fin n)) (X : Pt) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k →
    Cospherical ({P i j, P i k, P j k, X} : Set Pt)

/-- D1(a), Clifford n = 4: the four circles `Γ_123, Γ_124, Γ_134, Γ_234` have a common
point. -/
def classical_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) : Prop := 
    ∃ X : Pt, OnAllGamma P Finset.univ X


/-- D1(b), Clifford n = 5: the five Clifford points `X l` (of the four circles obtained by
omitting circle `l`) lie on one circle. -/
def classical_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) : Prop := 
    Cospherical (Set.range X)


/-- D1(c), Clifford n = 6: for each `m`, the five Clifford points `X m l` (`l ≠ m`) of the
five circles other than `m` lie on a circle `C m` (part (b)); these six circles have a
common point. `X m l` is the Clifford point of the four circles other than `m, l`. -/
def classical_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) : Prop := 
    ∃ Y : Pt, ∀ m, Y ∈ C m


/-- OWN DEFINITION. Data of Clifford's chain for `n` circles `c i` through `M`, levels
indexed by subsets `S` of the circles: `circ S` (for `|S|` odd) is the circle and `pt S`
(for `|S|` even) the point attached to `S`.
* level 1: `circ {i} = c i`;
* level 2: `pt {i,j}` is the second intersection of `c i, c j` (≠ `M`);
* odd level `|S| = 2k+1 ≥ 3`: `circ S` passes through the `|S|` points `pt (S \ {i})`,
  which are not collinear (general position), so `circ S` is uniquely determined;
* even level `|S| = 2k ≥ 4`: `pt S` lies on the `|S|` circles `circ (S \ {i})` and is their
  unique common point (general position).
All levels strictly below `n` are part of the data/hypotheses (they are the lower
instances of the chain); the theorems below assert the top level `n`. -/
structure CliffordChain (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt) : Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  level_one : ∀ i, circ {i} = c i
  level_two : ∀ S : Finset (Fin n), S.card = 2 →
    pt S ≠ M ∧ ∀ i ∈ S, pt S ∈ circ (S.erase i)
  odd_mem : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt (S.erase i) ∈ circ S
  odd_gp : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ¬ Collinear ℝ ((fun i => pt (S.erase i)) '' (S : Set (Fin n)))
  even_mem : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt S ∈ circ (S.erase i)
  even_gp : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ Y : Pt, (∀ i ∈ S, Y ∈ circ (S.erase i)) → Y = pt S

/-- D1(d), Clifford's chain, even step (all even `n ≥ 4`): the `n` circles of level
`n - 1` pass through one common point.
(The case `n = 2` is the general-position hypothesis `level_two` itself.) -/
def classical_D1_d_even (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ) : Prop := 
    ∃ Y : Pt, ∀ i, Y ∈ circ (Finset.univ.erase i)


/-- D1(d), Clifford's chain, odd step (all odd `n ≥ 3`): the `n` points of level `n - 1`
lie on one circle. -/
def classical_D1_d_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ)
    -- EXTRA HYPOTHESIS: the top-level points are not collinear ("one circle"). For `n = 3`
    -- this is exactly the non-collinearity hypothesis of (a).
    -- AMBIGUOUS: drop it and conclude `Cospherical … ∨ Collinear ℝ …` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range fun i => pt (Finset.univ.erase i))) : Prop := 
    Cospherical (Set.range fun i => pt (Finset.univ.erase i))


/-! ## D2 — Miquel's pentagram (five circles) theorem -/

/-- D2. Five lines `ℓ 0, …, ℓ 4` in general position (no two parallel, no three
concurrent), labelled in the cyclic order of the sides of the inner pentagon: its vertices
are `V i = ℓ i ∩ ℓ (i+1)`, the star points are `T i = ℓ (i-1) ∩ ℓ (i+1)`, and the outer
triangle `i` (bounded by `ℓ (i-1), ℓ i, ℓ (i+1)`) has vertices `V (i-1), V i, T i` and
circumcircle `ω i`.
AMBIGUOUS: the labelling is only required to be cyclic as above; we do not additionally
require the inner pentagon to be convex / the figure to be a "star" (alternative: add a
hypothesis that the `V i` form a convex pentagon with the `T i` outside it).
Consecutive circles `ω i, ω (i+1)` meet in the inner vertex `V i` and in
a second point `Q i`. Then the five points `Q i` lie on one circle. -/
def classical_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) : Prop := 
    Cospherical (Set.range Q)


/-- D2 obligation (well-formedness only): for five lines in general position the
intersection points `V i`, `T i` exist and the three vertices of each outer triangle are
non-collinear, so the circumcircles `ω i` exist (and are unique). -/
def classical_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) : Prop := 
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)


/-! ## D3 — Lester's theorem -/

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected OUTWARDLY on side
`q r` of triangle `p q r` (opposite side of line `q r` from `p`). -/
def IsOuterApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SOppSide p X

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected INWARDLY on side
`q r` of triangle `p q r` (same side of line `q r` as `p`). -/
def IsInnerApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SSameSide p X

/-- OWN DEFINITION. First Fermat point (first isogonic centre): common point of the lines
joining each vertex to the apex of the outward equilateral triangle on the opposite side. -/
def IsFirstFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsOuterApex a b c A' ∧ IsOuterApex b c a B' ∧ IsOuterApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- OWN DEFINITION. Second Fermat point (second isogonic centre): same with the inward
equilateral triangles. -/
def IsSecondFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsInnerApex a b c A' ∧ IsInnerApex b c a B' ∧ IsInnerApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- D3, Lester's theorem: in a scalene triangle the two Fermat points, the circumcentre and
the nine-point centre are concyclic. -/
def classical_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)


/-- D3 obligation (well-formedness only): both Fermat points exist (the second one needs
the triangle not to be equilateral; scalene suffices). -/
def classical_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) : Prop := 
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)


/-! ## D4 — Sawayama–Thébault theorem -/

/-- OWN DEFINITION. The circle `ω` (positive radius) is tangent to the line `p q`. -/
def TangentToLine (ω : Sphere Pt) (p q : Pt) : Prop :=
  0 < ω.radius ∧ Metric.infDist ω.center (line[ℝ, p, q] : Set Pt) = ω.radius

/-- OWN DEFINITION. The circle `ω` (positive radius) is internally tangent to the circle `Ω`
(lies inside `Ω` and touches it). -/
def InternallyTangent (ω Ω : Sphere Pt) : Prop :=
  0 < ω.radius ∧ ω.radius < Ω.radius ∧ dist ω.center Ω.center = Ω.radius - ω.radius

/-- D4, Sawayama–Thébault: `D` on side `BC`; `ω₁, ω₂` are tangent to lines `AD`, `BC`,
internally tangent to the circumcircle, one on each side of `AD`. Then their centres and
the incentre are collinear. -/
def classical_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt)


/-- D4 obligation (well-formedness only): the two Thébault circles exist. -/
def classical_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a


/-! ## D5 — Kosnita's theorem -/

/-- OWN DEFINITION. `o` is equidistant from `p, q, r`, i.e. (for `p, q, r` not collinear) the
circumcentre of triangle `p q r`. -/
def IsCircumcenterOf (o p q r : Pt) : Prop :=
  dist o p = dist o q ∧ dist o p = dist o r

/-- D5, Kosnita: with `O` the circumcentre and `O_a, O_b, O_c` the circumcentres of `OBC`,
`OCA`, `OAB`, the lines `AO_a, BO_b, CO_c` are concurrent.
(If `O` lies on a side — right triangle — the corresponding `O_x` does not exist and the
statement is vacuous; see the obligation.) -/
def classical_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc]))


/-- D5 obligation (well-formedness only): if the circumcentre is not on line `BC`, the
circumcentre of `OBC` exists. -/
def classical_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c


/-! ## D6 — Blundon's fundamental inequality -/

/-- D6, Blundon, lower bound. -/
def classical_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2


/-- D6, Blundon, upper bound. -/
def classical_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)


/-- D6 obligation (well-formedness only): the radicand is non-negative (Euler `R ≥ 2r`),
so `Real.sqrt` is the genuine square root rather than its junk value `0`. -/
def classical_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius


/-! ## D7 — Steiner–Lehmus theorem -/

/-- OWN DEFINITION. `e` is the foot of the internal bisector from vertex `v` of the angle
`p v q`: `e` lies on segment `p q` and bisects the angle at `v`. -/
def IsBisectorFoot (v p q e : Pt) : Prop :=
  Wbtw ℝ p e q ∧ ∠ p v e = ∠ e v q

/-- D7, Steiner–Lehmus: if the internal bisectors from `B` and `C` (vertex to opposite side)
have equal length, then `AB = AC`. -/
def classical_D7 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (e f : Pt)
    (he : IsBisectorFoot b a c e) (hf : IsBisectorFoot c a b f)
    (hlen : dist b e = dist c f) : Prop := 
    dist a b = dist a c


/-- D7 obligation (well-formedness only): the bisector foot exists. -/
def classical_D7_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    ∃ e, IsBisectorFoot b a c e


end Blundon.Classical

namespace Blundon.Classical

theorem cov_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2 := by
  exact (Blundon.blundon (⟨![a, b, c], h⟩ : Affine.Triangle ℝ Pt)).1


theorem cov_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) := by
  exact (Blundon.blundon (⟨![a, b, c], h⟩ : Affine.Triangle ℝ Pt)).2



open Blundon
 theorem cov_radicand_core {r R s x y z : ℝ} (hr : 0 < r) (hR : 0 < R) (hs0 : 0 < s)
    (hs : s = x + y + z) (h1 : r ^ 2 * s = x * y * z)
    (h2 : 4 * R * r * s = (y + z) * (z + x) * (x + y)) :
    0 ≤ R ^ 2 - 2 * R * r := by
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
  exact hrad

 theorem cov_triangle_radicand (t : Affine.Triangle ℝ Pt) :
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius := by
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
  refine cov_radicand_core (x := s - a) (y := s - b) (z := s - c) hr0 hR hs0 (by rw [hsp]; ring) ?_ ?_
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


theorem cov_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) :
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius := by
  exact cov_triangle_radicand ⟨![a,b,c],h⟩


end Blundon.Classical
