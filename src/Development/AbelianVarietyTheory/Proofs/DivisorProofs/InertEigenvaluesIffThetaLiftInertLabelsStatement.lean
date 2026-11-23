module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponentsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperatorsStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacesIffGoodPrimesFixedByConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertPlaces

theorem inert_places_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · rintro ⟨hg, hf⟩
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hg P (Or.inl hm)).1 rfl
    have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
      refine ⟨?_, hnS⟩
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
    obtain ⟨Q, hQ⟩ := h.inert.onto P hio
    refine ⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩
    · rw [hQ]; exact hio.1
    · rw [hQ]
      rintro (hm | hm)
      · exact hnS hm
      · exact (hg P (Or.inr hm)).1 rfl

end GlobalTheory.InertPlaces
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlacesIffGoodPrimesFixedByConjStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  first | exact @GlobalTheory.InertPlaces.inert_places_iff | exact GlobalTheory.InertPlaces.inert_places_iff | (intros; apply GlobalTheory.InertPlaces.inert_places_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorsCommonEigenvalueInertPrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertEig


open Classical in
noncomputable def coeff (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ) (b : List ℕ → ℂ) (d : List ℤ) : ℂ :=
  if h : ∃ s, ok s ∧ lab n s = d then b h.choose else 0

theorem coeff_cases {H : Type} [AddCommGroup H] [Module ℂ H] (n : ℕ) (ok : List ℕ → Prop) (lab : ℕ → List ℕ → List ℤ)
    (isLab : List ℤ → Prop) (hL : ∀ d, isLab d → ∃ s, ok s ∧ lab n s = d) (b : List ℕ → ℂ)
    (ops : List ℤ → Module.End ℂ H) (x : H) (hx : ∀ s, ok s → ops (lab n s) x = b s • x) (d : List ℤ) :
    (¬ isLab d ∧ coeff n ok lab b d = 0) ∨ ops d x = coeff n ok lab b d • x := by
  classical
  by_cases h : ∃ s, ok s ∧ lab n s = d
  · right
    have hf : coeff n ok lab b d = b h.choose := dif_pos h
    have h1 := hx _ h.choose_spec.1
    rw [h.choose_spec.2] at h1
    rw [hf]
    exact h1
  · left
    exact ⟨fun hl => h (hL d hl), dif_neg h⟩

theorem eig_of_single {H Γ ι W : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W]
    (e : H →ₗ[ℂ] (Γ → W)) (he : Function.Injective e) (rep : List ℤ → Finset ι) (act : Γ → ι → Γ)
    (ops : (List ℤ →₀ ℂ) → Module.End ℂ H)
    (hops : ∀ c x, e (ops c x) = fun g => c.sum fun d z => z • ∑ γ ∈ rep d, e x (act g γ))
    (f : List ℤ → ℂ) (x : H) (hx : ∀ d, (rep d = ∅ ∧ f d = 0) ∨ ops (Finsupp.single d 1) x = f d • x)
    (c : List ℤ →₀ ℂ) : ops c x = (c.sum fun d z => z * f d) • x := by
  have hd : ∀ d g, ∑ γ ∈ rep d, e x (act g γ) = f d • e x g := by
    intro d g
    rcases hx d with ⟨h0, hf⟩ | h1
    · rw [h0, hf, Finset.sum_empty, zero_smul]
    · have h2 := congrFun (hops (Finsupp.single d 1) x) g
      rw [h1, map_smul, Finsupp.sum_single_index (by simp), one_smul] at h2
      exact h2.symm
  apply he
  rw [hops c x, map_smul]
  funext g
  simp only [Pi.smul_apply, Finsupp.sum, hd, smul_smul, Finset.sum_smul]

theorem labIn_eq (n : ℕ) (s : List ℕ) : GlobalTheory.Hk3.labIn n s = labIn n s := rfl



theorem veig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hM j t hV hOps P hP hc b y y' hb cV
  have hL : ∀ d, IsLab (Vc D j) P d → ∃ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s ∧ labIn (Vc D j).rank s = d := by
    intro d hl
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hl
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank d).1 ⟨h1, h2, h3 hc⟩
    exact ⟨s, ⟨hs2, hs3, hs1⟩, (labIn_eq _ _).symm.trans hs4.symm⟩
  have hrep : ∀ d, ¬ IsLab (Vc D j) P d → GlobalTheory.Hk3.rep (Vc D j) P d = ∅ := by
    intro d hd
    classical
    exact dif_neg hd
  have key : ∀ x : (R.HV j t).H, (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s →
      hV P (Finsupp.single (labIn (Vc D j).rank s) 1) x = b s • x) →
      hV P cV x = (cV.sum fun d z => z * coeff (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn b d) • x := by
    intro x hx
    refine eig_of_single (R.HV j t).e (hM.HV j t).1 (GlobalTheory.Hk3.rep (Vc D j) P) (fun g γ => g * (finHom (Vc D j)).rangeRestrict γ)
      (hV P) (fun c x => hOps P hP c x) _ x ?_ cV
    intro d
    rcases coeff_cases (Vc D j).rank (Formalism.L2.Col.InertTypeOk (Vc D j).rank) labIn (IsLab (Vc D j) P) hL b
      (fun d => hV P (Finsupp.single d 1)) x hx d with ⟨h0, hf⟩ | h1
    · exact Or.inl ⟨hrep d h0, hf⟩
    · exact Or.inr h1
  exact ⟨_, key y (fun s hs => (hb s hs).1), key y' (fun s hs => (hb s hs).2)⟩

end GlobalTheory.InertEig
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalOperatorsCommonEigenvalueInertPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

theorem _root_.GlobalTheory.T.sphericalOperators_common_eigenvalue_inertPrime : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (j : Fin D.R.m) (t : T) (hV : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j t).H), GlobalTheory.Hk3.IsOpsV R j t hV → ∀ P, Good R t P → conjPl P = P → ∀ (b : List ℕ → ℂ) (y y' : (R.HV j t).H), (∀ s, Formalism.L2.Col.InertTypeOk (Vc D j).rank s → hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y = b s • y ∧ hV P (Finsupp.single (labIn (Vc D j).rank s) 1) y' = b s • y') → ∀ cV : List ℤ →₀ ℂ, ∃ σ : ℂ, hV P cV y = σ • y ∧ hV P cV y' = σ • y' := by
  first | exact @GlobalTheory.InertEig.veig | exact GlobalTheory.InertEig.veig | (intros; apply GlobalTheory.InertEig.veig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertEigenvaluesIffThetaLiftInertLabels

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertTransferW

theorem complex_smul_left_cancel_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {a b : ℂ} {w : V} (hw : w ≠ 0) (h : a • w = b • w) :
    a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

theorem field_smul_left_cancel_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {a b : K} {w : V} (hw : w ≠ 0)
    (h : a • w = b • w) : a = b := by
  by_contra hne
  apply hw
  have h2 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)



theorem inertEigenvalues_iff_thetaLift_inertLabels_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hE hS hTS hJunk j c c' u u' x x' hx hx' hc hc' hn hn'
  obtain ⟨hcore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hE
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hW0, hWops, -, -, -, -, hWev, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hcore hS hX R.SF hSF j
  obtain ⟨hV, hVops, -⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models).2 j A3.A.μ0
  have K : ∀ {cc : Pl D.host.E → List ℤ → ℂ} {z : (A3.A.fam.L j A3.A.μ0).S.Forms},
      R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ∈ R.Wc' j cc → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) ≠ 0 →
      ∀ P, Good R.toRealDat A3.A.μ0 P → ∀ cV cW, GlobalTheory.Hk3.MatchW R.toRealDat j A3.A.μ0 P cV cW → ∀ σ : ℂ,
      hV P cV (R.jV j A3.A.μ0 z) = σ • R.jV j A3.A.μ0 z → σ = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW := by
    intro cc z hz hz0 P hP cV cW hM σ hσ
    rw [hWc j cc] at hz
    have h1 := (GlobalTheory.T.theta_intertwines_matched_operators R.toRealDat F.lv2 hcore hS hX R.SF hSF j A3.A.μ0 P hP cV cW hM hV hVops).1 hW0 hWops
      (R.jV j A3.A.μ0 z)
    have h4 := hWev cc P hP cW _ hz
    have h5 : σ • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) = GlobalTheory.Hk3.evC (Wc D j) P (cc P) cW • R.thG j A3.A.μ0 (R.jV j A3.A.μ0 z) :=
      ((R.thG j A3.A.μ0).map_smul σ (R.jV j A3.A.μ0 z)).symm.trans ((congrArg (R.thG j A3.A.μ0) hσ).symm.trans (h1.trans h4))
    exact complex_smul_left_cancel_of_ne_zero hz0 h5
  have hrank : (Vc D j).rank = (A3.A.fam.L j A3.A.μ0).n := R.B.rankL j
  have V1 : ∀ (Q : A3.okI A3.A.μ0) (sq : List ℕ), Formalism.L2.Col.InertTypeOk (Vc D j).rank sq → ∀ f,
      R.jV j A3.A.μ0 (A3.heckeLI j A3.A.μ0 (Q, sq) f) =
        hV (R.plI Q) (Finsupp.single (labIn (Vc D j).rank sq) 1) (R.jV j A3.A.μ0 f) := by
    intro Q sq hsq f
    have tie := (hW.inert.hL j A3.A.μ0).some
    refine ((GlobalTheory.T.inertHeckeOperators_lifts_rational_selfAdjoint_labels R.toRealDat F.lv2 hcore.lev hcore.fam hcore.models j A3.A.μ0 _
      (fun k : A3.okI A3.A.μ0 × List ℕ => R.plI k.1) (fun k => labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) ?_ tie (Q, sq) hsq).2.2.2 hV hVops f)
    intro k hk
    obtain ⟨hg, hcj⟩ := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 (R.plI k.1)).1 ⟨k.1, k.1.2, rfl⟩
    refine ⟨hg, hcj, ?_⟩
    exact ((GlobalTheory.T.selfDual_antitone_list_iff_inertPrimeHeckeExponents (Vc D j).rank (labIn (Vc D j).rank k.2)).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simp)
  have hx0' : x' ≠ 0 := by rintro rfl; exact hn' (by simp)
  have hopx : ∀ k, A3.heckeLI j A3.A.μ0 k x = u (Sum.inr k) • x := fun k => hx (Sum.inr k)
  have hopx' : ∀ k, A3.heckeLI j A3.A.μ0 k x' = u' (Sum.inr k) • x' := fun k => hx' (Sum.inr k)
  constructor
  · intro hu P d hP hPc hd
    obtain ⟨Q, hQ, rfl⟩ := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 P).2 ⟨hP, hPc⟩
    obtain ⟨cV, hM⟩ := ((hTS _ hP hPc).2 j).2 (Finsupp.single d 1)
    obtain ⟨σ, h1, h2⟩ := GlobalTheory.T.sphericalOperators_common_eigenvalue_inertPrime R.toRealDat hcore.models j A3.A.μ0 hV hVops _ hP hPc
      (fun sq => D.what₂.embLL (u (Sum.inr (⟨Q, hQ⟩, sq)))) (R.jV j A3.A.μ0 x) (R.jV j A3.A.μ0 x')
      (fun sq hsq => ⟨(V1 ⟨Q, hQ⟩ sq hsq x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)),
        (V1 ⟨Q, hQ⟩ sq hsq x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans ((map_smulₛₗ _ _ _).trans
          (congrArg (fun a => D.what₂.embLL a • R.jV j A3.A.μ0 x') (hu _).symm)))⟩) cV
    have e1 := K hc hn _ hP cV _ hM σ h1
    have e2 := K hc' hn' _ hP cV _ hM σ h2
    unfold GlobalTheory.Hk3.evC at e1 e2
    rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul] at e1 e2
    exact e1.symm.trans e2
  · rintro hcc ⟨⟨Q0, hQ0⟩, sq⟩
    have hPl := (GlobalTheory.T.inert_places_iff_good_primes_fixed_by_conj R F hW A3.A.μ0 (R.plI Q0)).1 ⟨Q0, hQ0, rfl⟩
    rcases hJunk.2 j A3.A.μ0 (⟨Q0, hQ0⟩, sq) with h0 | ⟨y, hy, hop⟩
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) • x = 0 :=
        (hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x).trans (LinearMap.zero_apply x))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) • x' = 0 :=
        (hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun h0 x').trans (LinearMap.zero_apply x'))
      rw [(smul_eq_zero.mp a1).resolve_right hx0, (smul_eq_zero.mp a2).resolve_right hx0']
    · have a1 : u (Sum.inr (⟨Q0, hQ0⟩, sq)) = u (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0 ((hopx (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x).trans (hopx (⟨Q0, hQ0⟩, y))))
      have a2 : u' (Sum.inr (⟨Q0, hQ0⟩, sq)) = u' (Sum.inr (⟨Q0, hQ0⟩, y)) := by
        exact field_smul_left_cancel_of_ne_zero hx0' ((hopx' (⟨Q0, hQ0⟩, sq)).symm.trans ((LinearMap.congr_fun hop x').trans (hopx' (⟨Q0, hQ0⟩, y))))
      rw [a1, a2]
      rw [← hrank] at hy
      obtain ⟨cW, hM⟩ := ((hTS _ hPl.1 hPl.2).2 j).1 (Finsupp.single (labIn (Vc D j).rank y) 1)
      have b1 := K hc hn _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x).symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx _)).trans (map_smulₛₗ _ _ _)))
      have b2 := K hc' hn' _ hPl.1 _ cW hM _ ((V1 ⟨Q0, hQ0⟩ y hy x').symm.trans ((congrArg (R.jV j A3.A.μ0) (hopx' _)).trans (map_smulₛₗ _ _ _)))
      apply D.what₂.embLL.injective
      refine b1.trans (Eq.trans ?_ b2.symm)
      unfold GlobalTheory.Hk3.evC
      refine Finsupp.sum_congr fun d _ => ?_
      split_ifs with hd
      · rw [hcc _ d hPl.1 hPl.2 hd]
      · rfl

end GlobalTheory.InertTransferW
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertEigenvaluesIffThetaLiftInertLabelsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Good SchurAll TwoSided IsLab)

theorem _root_.GlobalTheory.T.inertEigenvalues_iff_thetaLift_inertLabels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  first | exact @GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt | exact GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt | (intros; apply GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt <;> assumption)
end
end
