import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCorePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangePf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsUnitEvalOfMapResidueNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ResidueNormValuationSubringEqZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SummableNormBoundedSeries

namespace GlobalTheory.DiscEval

open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries

section Series

variable {K : Type*} [NormedField K] [CompleteSpace K] {O : Type*} [CommRing O]
  (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) {t : K} (ht : ‖t‖ < 1)

omit [CompleteSpace K] in
include hi ht in
theorem summable_norm_term (f : O⟦X⟧) :
    Summable fun n : ℕ => ‖i (PowerSeries.coeff n f) * t ^ n‖ := by sorry





noncomputable def discEval : O⟦X⟧ →+* K := sorry


theorem hasSum_discEval (f : O⟦X⟧) :
    HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) := by sorry


@[simp] theorem discEval_C (a : O) : discEval i hi ht (PowerSeries.C a) = i a := by sorry





@[simp] theorem discEval_X : discEval i hi ht PowerSeries.X = t := by sorry





theorem norm_discEval_le_one [IsUltrametricDist K] (f : O⟦X⟧) : ‖discEval i hi ht f‖ ≤ 1 := by sorry





theorem norm_discEval_sub_le [IsUltrametricDist K] (f : O⟦X⟧) :
    ‖discEval i hi ht f - i (PowerSeries.constantCoeff f)‖ ≤ ‖t‖ := by sorry





theorem discEval_mem {B : Subring K} (hB : IsClosed (B : Set K)) (hiB : ∀ x, i x ∈ B)
    (htB : t ∈ B) (f : O⟦X⟧) : discEval i hi ht f ∈ B := by sorry



end Series

section Away

variable {K : Type*} {O : Type*} [CommRing O] (π : O)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

section Laurent

variable [Field K] (i : O →+* K) (hπ : i π ≠ 0)

noncomputable def laurent : A →+* K⸨X⸩ := sorry







@[simp] theorem laurent_algebraMap (f : O⟦X⟧) :
    laurent π A i hπ (algebraMap O⟦X⟧ A f) = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map i f) := by sorry


variable {π A}

theorem coeff_laurent {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀)
    (n : ℤ) : (laurent π A i hπ f).coeff n =
      if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀) := by sorry

















end Laurent

theorem exists_mul_eq (f : A) : ∃ (a b : ℕ) (f₀ : O⟦X⟧),
    f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ := by sorry



section Value

variable [NormedField K] [CompleteSpace K] (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)

noncomputable def discEvalAway : A →+* K := sorry




@[simp] theorem discEvalAway_algebraMap (f : O⟦X⟧) :
    discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f := by sorry


variable {π A}

theorem discEvalAway_eq {f : A} {a b : ℕ} {f₀ : O⟦X⟧}
    (h : f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀) :
    discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ := by sorry





theorem hasSum_laurent (f : A) :
    HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
      (discEvalAway π A i hi hπ ht0 ht f) := by sorry













include hi ht0 ht in

theorem tendsto_norm_laurent_term (f : A) :
    Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) := by sorry


theorem discEvalAway_mem {B : Subfield K} (hB : IsClosed (B : Set K)) (hiB : ∀ x, i x ∈ B)
    (htB : t ∈ B) (f : A) : discEvalAway π A i hi hπ ht0 ht f ∈ B := by sorry





end Value

end Away

section Coefficients

open MvPolynomial

variable {K : Type*} [Field K] {σ τ : Type*}

noncomputable def coeffPoly (m : ℤ) (G : MvPolynomial σ K⸨X⸩) : MvPolynomial σ K := sorry


@[simp] theorem coeff_coeffPoly (m : ℤ) (G : MvPolynomial σ K⸨X⸩) (μ : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffPoly m G) μ = (AddMonoidAlgebra.coeff G μ).coeff m := by sorry






theorem coeffPoly_sum {α : Type*} (m : ℤ) (s : Finset α) (G : α → MvPolynomial σ K⸨X⸩) :
    coeffPoly m (∑ a ∈ s, G a) = ∑ a ∈ s, coeffPoly m (G a) := by sorry



theorem coeffPoly_C_mul_map (m : ℤ) (c : K⸨X⸩) (Q : MvPolynomial σ K) :
    coeffPoly m (C c * map (HahnSeries.C : K →+* K⸨X⸩) Q) = C (c.coeff m) * Q := by sorry




theorem coeffPoly_bind₁ (m : ℤ) (g : σ → MvPolynomial τ K) (G : MvPolynomial σ K⸨X⸩) :
    coeffPoly m (bind₁ (fun k => map (HahnSeries.C : K →+* K⸨X⸩) (g k)) G) =
      bind₁ g (coeffPoly m G) := by sorry






theorem isHomogeneous_coeffPoly (m : ℤ) {G : MvPolynomial σ K⸨X⸩} {d : ℕ}
    (hG : G.IsHomogeneous d) : (coeffPoly m G).IsHomogeneous d := by sorry


theorem exists_coeffPoly_eq_zero (G : MvPolynomial σ K⸨X⸩) :
    ∃ b : ℕ, ∀ m : ℤ, m < -(b : ℤ) → coeffPoly m G = 0 := by sorry








end Coefficients

section Core

open MvPolynomial

variable {O : Type*} [CommRing O] {π : O}
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

theorem hasSum_coeffPoly {K : Type*} [NormedField K] [CompleteSpace K] (i : O →+* K)
    (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1) {σ : Type*}
    (F : MvPolynomial σ A) (x : σ → K) :
    HasSum (fun m : ℤ => eval x (coeffPoly m (map (laurent π A i hπ) F)) * t ^ m)
      (eval₂ (discEvalAway π A i hi hπ ht0 ht) x F) := by sorry

















theorem norm_coeff_bind₁_le {K : Type*} [NormedField K] [IsUltrametricDist K] {σ τ : Type*}
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) (hP1 : ∀ μ, ‖AddMonoidAlgebra.coeff P μ‖ ≤ 1)
    {g : σ → MvPolynomial τ K} {c : ℝ} (hc : 0 ≤ c) (hg : ∀ k μ, ‖AddMonoidAlgebra.coeff (g k) μ‖ ≤ c)
    (μ : τ →₀ ℕ) : ‖AddMonoidAlgebra.coeff (bind₁ g P) μ‖ ≤ c ^ d := by sorry















variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_detProdPoly_le {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] (μ : EntryIndex n n →₀ ℕ) : ‖AddMonoidAlgebra.coeff (detProdPoly K n) μ‖ ≤ 1 := by sorry










theorem exists_norm_coeff_detProdPoly {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : ∃ μ, ‖AddMonoidAlgebra.coeff (detProdPoly K n) μ‖ = 1 := by sorry

















variable [CompleteSpace K]

theorem coeffPoly_integral_of_admissible (K₀ : Subfield K)
    (hres : ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K)) (S : Set K)
    (hS : ∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1)
    (hdense : ∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε)
    (hrot : ∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S)
    (i : O →+* K) (hi : ∀ x, ‖i x‖ ≤ 1) (hπ : i π ≠ 0) {σ : Type} [Fintype σ]
    (δ : MvPolynomial σ K) (hδ : ∀ μ, ‖AddMonoidAlgebra.coeff δ μ‖ ≤ 1) (hδ1 : ∃ μ, ‖AddMonoidAlgebra.coeff δ μ‖ = 1)
    (F : MvPolynomial σ A)
    (hF : ∀ t ∈ S, ∀ (ht0 : t ≠ 0) (ht : ‖t‖ < 1) (x : σ → K), (∀ k, x k ∈ K₀ ∧ ‖x k‖ ≤ 1) →
      ‖eval x δ‖ = 1 → ‖eval₂ (discEvalAway π A i hi hπ ht0 ht) x F‖ ≤ 1) (m : ℤ) :
    (∀ μ, ‖AddMonoidAlgebra.coeff (coeffPoly m (map (laurent π A i hπ) F)) μ‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by sorry









end Core

section Padic

theorem exists_comp_eq_of_mem_range {R B K : Type*} [CommRing R] [CommRing B] [CommRing K]
    (e : B →+* K) (he : Function.Injective e) (φ : R →+* K) (h : ∀ a, φ a ∈ e.range) :
    ∃ ψ : R →+* B, ∀ a, e (ψ a) = φ a := by sorry





theorem residueFieldInfiniteOn_fieldRange {C K : Type*} [NormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [NormedField K] [IsUltrametricDist K] (e : C →+* K) (he : ∀ x, ‖e x‖ = ‖x‖) :
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (e.fieldRange : Set K) := by sorry



















theorem exists_abs_norm_sub_lt {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {r ε : ℝ}
    (h0 : 0 < r) (h1 : r < 1) (hε : 0 < ε) : ∃ x : C, 0 < ‖x‖ ∧ ‖x‖ < 1 ∧ |‖x‖ - r| < ε := by sorry










variable (p : ℕ) [Fact p.Prime]

noncomputable def algField : Subfield ℂ_[p] := sorry

def algDisc : Set ℂ_[p] := sorry

theorem residueFieldInfiniteOn_algField :
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (algField p : Set ℂ_[p]) := by sorry


theorem algDisc_dense (r : ℝ) (h0 : 0 < r) (h1 : r < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ algDisc p, |‖t‖ - r| < ε := by sorry




theorem mul_mem_algDisc (t : ℂ_[p]) (ht : t ∈ algDisc p) (τ : ℂ_[p]) (hτ : τ ∈ algField p)
    (hτ1 : ‖τ‖ = 1) : t * τ ∈ algDisc p := by sorry


variable {p}

theorem mem_algField_iff {x : ℂ_[p]} : x ∈ algField p ↔ IsIntegral ℚ_[p] x := by sorry








theorem ringHom_padicInt_eq (g : ℤ_[p] →+* ℂ_[p]) (hg : ∀ z, ‖g z‖ ≤ 1) (z : ℤ_[p]) :
    g z = algebraMap ℚ_[p] ℂ_[p] z := by sorry





















noncomputable def fieldEmb (L : IntermediateField ℚ_[p] (PadicAlgCl p)) : L →+* ℂ_[p] := sorry


noncomputable def intEmb (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    integralClosure ℤ_[p] L →+* ℂ_[p] := sorry


section Field

variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem fieldEmb_apply (x : L) : fieldEmb L x = ((x : PadicAlgCl p) : ℂ_[p]) := by sorry

theorem intEmb_apply (x : integralClosure ℤ_[p] L) : intEmb L x = fieldEmb L x := by sorry

theorem intEmb_injective : Function.Injective (intEmb L) := by sorry


theorem fieldEmb_mem_algField (x : L) : fieldEmb L x ∈ algField p := by sorry

theorem mem_integralClosure_iff_norm (x : L) : x ∈ integralClosure ℤ_[p] L ↔ ‖fieldEmb L x‖ ≤ 1 := by sorry


theorem norm_intEmb_le_one (x : integralClosure ℤ_[p] L) : ‖intEmb L x‖ ≤ 1 := by sorry


theorem mem_range_intEmb_iff (x : ℂ_[p]) :
    x ∈ (intEmb L).range ↔ x ∈ (fieldEmb L).fieldRange ∧ ‖x‖ ≤ 1 := by sorry






variable [FiniteDimensional ℚ_[p] L]

theorem mem_maximalIdeal_iff_norm (x : integralClosure ℤ_[p] L) :
    x ∈ maximalIdeal (integralClosure ℤ_[p] L) ↔ ‖intEmb L x‖ < 1 := by sorry


theorem isUnit_iff_norm (x : integralClosure ℤ_[p] L) : IsUnit x ↔ ‖intEmb L x‖ = 1 := by sorry



theorem isClosed_fieldRange : IsClosed ((fieldEmb L).fieldRange : Set ℂ_[p]) := by sorry



theorem isAdicComplete_integralClosure :
    IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] L)) (integralClosure ℤ_[p] L) := by sorry




















theorem finite_residueField_integralClosure :
    Finite (ResidueField (integralClosure ℤ_[p] L)) := by sorry





end Field

section Finite

variable {O : Type*} [CommRing O] [Algebra ℤ_[p] O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1)

include hi in

theorem map_algebraMap_padicInt (z : ℤ_[p]) :
    i (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] ℂ_[p] z := by sorry


noncomputable def genField (T : Set ℂ_[p]) : IntermediateField ℚ_[p] (PadicAlgCl p) := sorry


variable [Module.Finite ℤ_[p] O]

include hi

theorem map_mem_algField (x : O) : i x ∈ algField p := by sorry






theorem fieldRange_genField {T : Set ℂ_[p]} (hT : T ⊆ algField p) :
    (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) := by sorry


















theorem map_mem_genField {T : Set ℂ_[p]} (hT : T ⊆ algField p) (x : O) :
    i x ∈ (fieldEmb (genField i T)).fieldRange := by sorry



theorem mem_genField_of_mem {T : Set ℂ_[p]} (hT : T ⊆ algField p) {x : ℂ_[p]} (hx : x ∈ T) :
    x ∈ (fieldEmb (genField i T)).fieldRange := by sorry



theorem finiteDimensional_genField {T : Set ℂ_[p]} (hT : T.Finite) :
    FiniteDimensional ℚ_[p] (genField i T) := by sorry



























variable (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]

omit [Module.Finite ℤ_[p] O] in

theorem finite_of_intEmb_eq {j : O →+* integralClosure ℤ_[p] L} (hj : ∀ a, intEmb L (j a) = i a) :
    j.Finite := by sorry








omit [Module.Finite ℤ_[p] O] in
theorem isLocalHom_of_intEmb_eq (hinj : Function.Injective i)
    {j : O →+* integralClosure ℤ_[p] L} (hj : ∀ a, intEmb L (j a) = i a) : IsLocalHom j := by sorry



theorem norm_map_eq_one_iff (hinj : Function.Injective i) (x : O) : ‖i x‖ = 1 ↔ IsUnit x := by sorry






omit [Module.Finite ℤ_[p] O] [Algebra ℤ_[p] O] in

theorem exists_intEmb_eq_discEval (hiL : ∀ x, i x ∈ (fieldEmb L).fieldRange) {t : ℂ_[p]}
    (htL : t ∈ (fieldEmb L).fieldRange) (ht : ‖t‖ < 1) :
    ∃ ev : O⟦X⟧ →+* integralClosure ℤ_[p] L, ∀ f, intEmb L (ev f) = discEval i hi ht f := by sorry




omit [Module.Finite ℤ_[p] O] in

theorem isLocalHom_of_intEmb_eq_discEval (hinj : Function.Injective i) {t : ℂ_[p]} (ht : ‖t‖ < 1)
    {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} (hev : ∀ f, intEmb L (ev f) = discEval i hi ht f) :
    IsLocalHom ev := by sorry










end Finite

theorem exists_injective_norm_le_one (O : Type*) [CommRing O] [IsDomain O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (hp : (p : O) ≠ 0) :
    ∃ i : O →+* ℂ_[p], Function.Injective i ∧ ∀ x, ‖i x‖ ≤ 1 := by sorry



section Points

variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  (A : Type*) [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]

def IsDiscPoint (L : IntermediateField ℚ_[p] (PadicAlgCl p)) {t : ℂ_[p]} (ht0 : t ≠ 0)
    (ht : ‖t‖ < 1) (ev : O⟦X⟧ →+* integralClosure ℤ_[p] L) (evA : A →+* L) : Prop := sorry



variable {i hi hπ A} in

theorem IsDiscPoint.comp_algebraMap {L : IntermediateField ℚ_[p] (PadicAlgCl p)} {t : ℂ_[p]}
    {ht0 : t ≠ 0} {ht : ‖t‖ < 1} {ev : O⟦X⟧ →+* integralClosure ℤ_[p] L} {evA : A →+* L}
    (h : IsDiscPoint i hi hπ A L ht0 ht ev evA) :
    evA.comp (algebraMap O⟦X⟧ A) = (algebraMap (integralClosure ℤ_[p] L) L).comp ev := by sorry




theorem exists_isDiscPoint (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
    (hiL : ∀ x, i x ∈ (fieldEmb L).fieldRange) {t : ℂ_[p]} (htL : t ∈ (fieldEmb L).fieldRange)
    (ht0 : t ≠ 0) (ht : ‖t‖ < 1) : ∃ ev evA, IsDiscPoint i hi hπ A L ht0 ht ev evA := by sorry






end Points

section Frames

open MvPolynomial

variable (p) in

def algInt : Subring ℂ_[p] where
  carrier := sorry








theorem isUnit_algInt_iff (x : algInt p) : IsUnit x ↔ ‖(x : ℂ_[p])‖ = 1 := by sorry











variable {O : Type*} [CommRing O] (i : O →+* ℂ_[p]) (hi : ∀ x, ‖i x‖ ≤ 1) {π : O} (hπ : i π ≠ 0)
  {A : Type*} [CommRing A] [Algebra O⟦X⟧ A]
  [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A]
  {ι : Type} [Fintype ι] {n : ι → Type} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]

def BoundedOnFrames (F : MvPolynomial (EntryIndex n n) A) : Prop := sorry




def IntegralOnFrames (F : MvPolynomial (EntryIndex n n) A) : Prop := sorry






theorem boundedOnFrames_iff_integralOnFrames [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (F : MvPolynomial (EntryIndex n n) A) :
    BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F := by sorry








































variable {i hi hπ} {F : MvPolynomial (EntryIndex n n) A}

theorem BoundedOnFrames.coeffPoly_integral (hF : BoundedOnFrames i hi hπ F) (m : ℤ) :
    (∀ μ, ‖AddMonoidAlgebra.coeff (coeffPoly m (map (laurent π A i hπ) F)) μ‖ ≤ 1) ∧
      (m < 0 → coeffPoly m (map (laurent π A i hπ) F) = 0) := by sorry












theorem BoundedOnFrames.norm_coeff_bind₁_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {τ : Type*} {g : EntryIndex n n → MvPolynomial τ ℂ_[p]} {c : ℝ}
    (hc : 0 ≤ c) (hg : ∀ k μ, ‖AddMonoidAlgebra.coeff (g k) μ‖ ≤ c) (μ : τ →₀ ℕ) (m : ℤ) :
    ‖(AddMonoidAlgebra.coeff (bind₁ (fun k => map HahnSeries.C (g k)) (map (laurent π A i hπ) F)) μ).coeff m‖ ≤
        c ^ d ∧
      (m < 0 → (AddMonoidAlgebra.coeff (bind₁ (fun k => map HahnSeries.C (g k))
        (map (laurent π A i hπ) F)) μ).coeff m = 0) := by sorry




theorem BoundedOnFrames.norm_coeff_linear_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {B : EntryIndex n n → EntryIndex n n → ℂ_[p]} {c : ℝ}
    (hc : 1 ≤ c) (hB : ∀ k l, ‖B k l‖ ≤ c) (μ : EntryIndex n n →₀ ℕ) (m : ℤ) :
    ‖(AddMonoidAlgebra.coeff (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F)) μ).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (AddMonoidAlgebra.coeff (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
        (map (laurent π A i hπ) F)) μ).coeff m = 0) := by sorry









theorem BoundedOnFrames.norm_coeff_mul_le (hF : BoundedOnFrames i hi hπ F) {d : ℕ}
    (hd : F.IsHomogeneous d) {κ : ι → Type*} [∀ s, Fintype (κ s)]
    {w : ∀ s, Matrix (n s) (κ s) ℂ_[p]} {c : ℝ} (hc : 0 ≤ c) (hw : ∀ s a b, ‖w s a b‖ ≤ c)
    (μ : EntryIndex κ n →₀ ℕ) (m : ℤ) :
    ‖(AddMonoidAlgebra.coeff (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F)) μ).coeff m‖ ≤ c ^ d ∧
      (m < 0 → (AddMonoidAlgebra.coeff (bind₁ (fun k => ∑ j, C (HahnSeries.C (w k.1 k.2.1 j)) * X ⟨k.1, j, k.2.2⟩)
        (map (laurent π A i hπ) F)) μ).coeff m = 0) := by sorry













theorem boundedOnFrames_map (F₀ : MvPolynomial (EntryIndex n n) O⟦X⟧) :
    BoundedOnFrames i hi hπ (map (algebraMap O⟦X⟧ A) F₀) := by sorry










end Frames

end Padic

open MvPolynomial in

theorem main (p : ℕ) [Fact p.Prime] :
    (ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (algField p : Set ℂ_[p]) ∧
      (∀ t ∈ algDisc p, 0 < ‖t‖ ∧ ‖t‖ < 1) ∧
      (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ algDisc p, |‖t‖ - r| < ε) ∧
      ∀ t ∈ algDisc p, ∀ τ ∈ algField p, ‖τ‖ = 1 → t * τ ∈ algDisc p) ∧
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] (i : O →+* ℂ_[p])
      (hi : ∀ x, ‖i x‖ ≤ 1) (_ : Function.Injective i) (π : O) (hπ : i π ≠ 0)
      (A : Type) [CommRing A] [Algebra O⟦X⟧ A]
      [IsLocalization.Away (PowerSeries.C π * PowerSeries.X : O⟦X⟧) A],
      (∀ (t : ℂ_[p]) (ht0 : t ≠ 0) (ht : ‖t‖ < 1),
        (∀ f : O⟦X⟧,
          HasSum (fun n : ℕ => i (PowerSeries.coeff n f) * t ^ n) (discEval i hi ht f) ∧
          discEvalAway π A i hi hπ ht0 ht (algebraMap O⟦X⟧ A f) = discEval i hi ht f) ∧
        (∀ T : Set ℂ_[p], T.Finite → T ⊆ algField p → t ∈ T →
          (fieldEmb (genField i T)).fieldRange = Subfield.closure (Set.range i ∪ T) ∧
          ∃ (_ : FiniteDimensional ℚ_[p] (genField i T))
            (_ : IsDiscreteValuationRing (integralClosure ℤ_[p] (genField i T))),
            IsAdicComplete (maximalIdeal (integralClosure ℤ_[p] (genField i T)))
              (integralClosure ℤ_[p] (genField i T)) ∧
            Finite (ResidueField (integralClosure ℤ_[p] (genField i T))) ∧
            IsFractionRing (integralClosure ℤ_[p] (genField i T)) (genField i T) ∧
            ∃ (ev : O⟦X⟧ →+* integralClosure ℤ_[p] (genField i T)) (evA : A →+* genField i T),
              (∀ f, intEmb _ (ev f) = discEval i hi ht f) ∧
              (∀ f, fieldEmb _ (evA f) = discEvalAway π A i hi hπ ht0 ht f) ∧
              evA.comp (algebraMap O⟦X⟧ A) = (algebraMap _ (genField i T)).comp ev ∧
              IsLocalHom ev ∧ (ev.comp PowerSeries.C).Finite ∧
              IsLocalHom (ev.comp PowerSeries.C)) ∧
        (∀ f : A,
          Tendsto (fun n : ℤ => ‖(laurent π A i hπ f).coeff n * t ^ n‖) cofinite (𝓝 0) ∧
          HasSum (fun n : ℤ => (laurent π A i hπ f).coeff n * t ^ n)
            (discEvalAway π A i hi hπ ht0 ht f)) ∧
        ∀ (f : A) (a b : ℕ) (f₀ : O⟦X⟧),
          f * algebraMap O⟦X⟧ A (PowerSeries.C π ^ a * PowerSeries.X ^ b) = algebraMap O⟦X⟧ A f₀ →
          discEvalAway π A i hi hπ ht0 ht f = (i π)⁻¹ ^ a * t⁻¹ ^ b * discEval i hi ht f₀ ∧
          ∀ n : ℤ, (laurent π A i hπ f).coeff n =
            if n + b < 0 then 0 else (i π)⁻¹ ^ a * i (PowerSeries.coeff (n + b).natAbs f₀)) ∧
      ∀ (ι : Type) [Fintype ι] (n : ι → Type) [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]
        (F : MvPolynomial (EntryIndex n n) A),
        (BoundedOnFrames i hi hπ F ↔ IntegralOnFrames i hi hπ F) ∧
        ∀ d : ℕ, F.IsHomogeneous d → BoundedOnFrames i hi hπ F →
          ∀ (B : EntryIndex n n → EntryIndex n n → ℂ_[p]) (c : ℝ), 1 ≤ c → (∀ k l, ‖B k l‖ ≤ c) →
            ∀ (μ : EntryIndex n n →₀ ℕ) (m : ℤ),
              ‖(coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m‖ ≤ c ^ d ∧
              (m < 0 → (coeff μ (bind₁ (fun k => ∑ l, C (HahnSeries.C (B k l)) * X l)
                (map (laurent π A i hπ) F))).coeff m = 0) := by sorry




























end GlobalTheory.DiscEval
