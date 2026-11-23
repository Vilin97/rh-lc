module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityCoverFunctionReferenceTupleStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormClassSumNormalisedData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOneMapBaseTupleOfCharacterisationExtremalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapCommutesFieldAutomorphismStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMapEveryNormalisedFamilyAtCoreConstantsStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleLiftsEquivariantRootOfUnity

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option autoImplicit false

namespace GlobalTheory.ConjRefLift

section Scale

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {c : ℂ} (hc : c ≠ 0)
    {Ψ Ψ' Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ 1 Ψ Ψ') (e : ∀ g, Φ g = c⁻¹ * Ψ g)
    (e' : ∀ g, Φ' g = (τ c)⁻¹ * Ψ' g) : ConjFun O κ τ 1 Φ Φ' := by
  obtain ⟨⟨n, a, f, ha⟩, hall⟩ := h
  have hτc : τ c ≠ 0 := (map_ne_zero τ).2 hc
  refine ⟨⟨n, fun k => c⁻¹ * a k, f, fun g => ?_⟩, fun m b f' hb g => ?_⟩
  · rw [e g, ha g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have hb' : Expands O κ Ψ (fun k => c * b k) f' := fun g => by
      have h1 := hb g
      rw [e g] at h1
      have h2 : Ψ g = c * (c⁻¹ * Ψ g) := by field_simp
      rw [h2, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e' g, hall m _ f' hb' g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, one_mul]
    field_simp

theorem conjFun_congr {Tp' : Type} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup) (O' : OMDat T.toCore R i Tp' tup')
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ}
    (hphi : O.phi (T.cE ((i : ℕ) + 1) O.s0) = O'.phi (T.cE ((i : ℕ) + 1) O'.s0)) (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands at h ⊢
  rw [← hphi]
  exact h

end Scale



theorem conjFun_lifts_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs c₀ hc₀ hc₀P
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hrow0 := GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hC D G Pl0 T0 A T R F κ v₀ hcore hT hio O i hpins
  have hEqO := (hphase hrow0).1
  have elev : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hMl]
  have hEq : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), elev]
    exact hEqO
  obtain ⟨ζ, z, hζ, -, hser⟩ :=
    GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin ⟨fw⟩ hio hQ i hpins hphase T0 id M hMp hMl hMe
  obtain ⟨nζ, hnζ, hζn⟩ := hζ
  obtain ⟨nc, hnc, hcn⟩ := hc₀
  have hζ0 : ζ ≠ 0 := fun h0 => by simp [h0, hnζ.ne'] at hζn
  have hc0 : ((c₀ : M.c'.F) : ℂ) ≠ 0 := fun h0 => by simp [h0, hnc.ne'] at hcn
  refine ⟨(ζ * (c₀ : ℂ))⁻¹, ⟨nζ * nc, Nat.mul_pos hnζ hnc, ?_⟩, fun τ ta hta hB y y' hyy => ?_⟩
  · rw [inv_pow, mul_pow, pow_mul, hζn, one_pow, mul_comm nζ nc, pow_mul, hcn, one_pow, mul_one, inv_one]
  have hf : Fixes M.c' ta :=
    fixes_of_le (c := T.Q.c) ta fun x hx => Subtype.ext ((hta x).trans (hB.core ⟨x, hx⟩))
  obtain ⟨h, J', hR, -⟩ := (hMp.tuple A.μ0).reps
  choose x x' hxx hx hx' using fun k => hyy (h k)
  have hio' : ∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k)) := fun k =>
    GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB (x k) (x' k) (hxx k)
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hC D G Pl0 T0 A T R F κ v₀ hcore hT i T0 id M hMp A.μ0 x
  obtain ⟨f, hf2⟩ := hex
  have hfc := hf2.1
  have hfs := hf2.2
  have hfsec : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hP' := hc₀P τ ta hta hB hf x x' hio' f hfsec hfs
  have e1 := hser A.μ0 h J' hR y x hx f hfsec hfs
  have e2 := hser A.μ0 h J' hR y' x' hx' _ hP'.1 hP'.2
  dsimp only [id_eq] at e1 e2
  have hCM := GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB hf z f hfc hEq
  have hsm : ∀ (s : M.c'.F) (Fr : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') a b,
      rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (s • Fr)) a b =
        inC M.c' s * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z Fr) a b := by
    intro s Fr a b
    rw [map_smul, map_smulₛₗ]
    rfl
  have hcv : inC M.c' c₀ = (c₀ : ℂ) := rfl
  have htv : inC M.c' (ta c₀) = τ (c₀ : ℂ) := hta c₀
  have hτ0 : τ (c₀ : ℂ) ≠ 0 := (map_ne_zero τ).2 hc0
  refine conjFun_scale (O i) (κ i) τ hc0 (conjFun_congr M (O i) (GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1))) hCM)
    (fun g => ?_) (fun g => ?_)
  · beta_reduce
    rw [mul_assoc, e1 g]
    field_simp
  · beta_reduce
    have hs := hsm ((ta c₀ * c₀⁻¹)⁻¹) (galRul hf f) (M.dict g).1 (M.dict g).2
    rw [mul_assoc, e2 g]
    erw [hs]
    rw [map_inv₀, map_mul, map_inv₀, hcv, htv]
    field_simp

end GlobalTheory.ConjRefLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleLiftsEquivariantRootOfUnityStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  first | exact @GlobalTheory.ConjRefLift.conjFun_lifts_root | exact GlobalTheory.ConjRefLift.conjFun_lifts_root | (intros; apply GlobalTheory.ConjRefLift.conjFun_lifts_root <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot

section

@[expose] public section

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRefTup

section IdempotentCombination
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ)

theorem conj_sum_eq (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ : GA D (Wc D i) → ℂ} {n m : ℕ} {a : Fin n → ℂ}
    {b : Fin m → ℂ} {f : Fin n → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n} {g : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA κ) κ.n}
    (ha : Expands O κ Φ a f) (hb : Expands O κ Φ b g) (x : GA D (Wc D i)) :
    ∑ k, τ (a k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (f k : T.toCore.R ((i : ℕ) + 1)) x) =
    ∑ k, τ (b k) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
      O.phi (T.cE ((i : ℕ) + 1) O.s0) (g k : T.toCore.R ((i : ℕ) + 1)) x) := by
  have h0 : Expands O κ (fun _ => 0) (Fin.append a (fun k => -b k)) (Fin.append f g) := by
    intro y
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    rw [← ha y, ← hb y, add_neg_cancel]
  have h1 := hZ.2 _ _ _ h0 x
  rw [Fin.sum_univ_add] at h1
  simp only [Fin.append_left, Fin.append_right, map_neg, one_mul, neg_mul, Finset.sum_neg_distrib] at h1
  linear_combination (-1 : ℂ) * h1

theorem conjFun_lin (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) {Φ Φ' Ψ Ψ' : GA D (Wc D i) → ℂ}
    (h1 : ConjFun O κ τ 1 Φ Φ') (h2 : ConjFun O κ τ 1 Ψ Ψ') (c d : ℂ) :
    ConjFun O κ τ 1 (fun x => c * Φ x + d * Ψ x) (fun x => τ c * Φ' x + τ d * Ψ' x) := by
  obtain ⟨n, a, f, ha⟩ := h1.1
  obtain ⟨m, b, g, hb⟩ := h2.1
  have hs : Expands O κ (fun x => c * Φ x + d * Ψ x) (Fin.append (fun k => c * a k) (fun k => d * b k)) (Fin.append f g) := by
    intro x
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [ha x, hb x, Finset.mul_sum, Finset.mul_sum]
    simp only [mul_assoc]
  refine ⟨⟨_, _, _, hs⟩, fun N e h he x => ?_⟩
  simp only [one_mul]
  rw [conj_sum_eq O κ τ hZ he hs x, Fin.sum_univ_add, h1.2 _ _ _ ha x, h2.2 _ _ _ hb x]
  simp only [Fin.append_left, Fin.append_right, one_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem conjFun_sum (hZ : ConjFun O κ τ 1 (fun _ => 0) (fun _ => 0)) : ∀ (n : ℕ) (α : Fin n → ℂ)
    (Φ Φ' : Fin n → GA D (Wc D i) → ℂ), (∀ k, ConjFun O κ τ 1 (Φ k) (Φ' k)) →
    ConjFun O κ τ 1 (fun g => ∑ k, α k * Φ k g) (fun g => ∑ k, τ (α k) * Φ' k g) := by
  intro n
  induction n with
  | zero => intro α Φ Φ' _; simpa using hZ
  | succ n ih =>
    intro α Φ Φ' hk
    have h := conjFun_lin O κ τ hZ (hk 0) (ih (fun k => α k.succ) (fun k => Φ k.succ) (fun k => Φ' k.succ)
      (fun k => hk k.succ)) (α 0) 1
    simp only [map_one, one_mul] at h
    simpa only [Fin.sum_univ_succ] using h

end IdempotentCombination



theorem conjFun_base_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∀ y y' : (R.HV i A.μ0).H, ConjForm R i τ c A.μ0 A.μ0 y y' → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase c hc
  have h2 := GlobalTheory.T.exists_normalisedData_normalCoefficientField D G Pl0 T0 A T R F κ v₀ O hcore hfin hfw hQ i hpins
  obtain ⟨M, hMp, hMl, hMe, hMn, hMc, hMx, hMs⟩ := h2
  have h3 := GlobalTheory.T.exists_rootOfUnity_coverFunction_reference_tuple hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs
  have h4 := GlobalTheory.T.referenceTuple_lifts_equivariant_rootOfUnity hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs h3.choose h3.choose_spec.1 h3.choose_spec.2
  refine ⟨h4.choose, h4.choose_spec.1, fun τ hB y y' hyy => ?_⟩
  have hP := h4.choose_spec.2
  let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  haveI := hMn
  let ta : M.c'.F ≃+* M.c'.F := (τa.restrictNormal M.c'.F).toRingEquiv
  have hta : ∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ) := fun a => AlgEquiv.restrictNormal_commutes τa M.c'.F a
  have hct : ConjTup R τ A.μ0 A.μ0 := by
    refine ⟨rfl, fun x => ?_⟩
    have h1 := hcore.lev.xi A.μ0
    rw [hcore.lev.xi_base] at h1
    rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 x]
    simp
  have h5 := GlobalTheory.T.conjugate_definiteForms_descend_numberField D G Pl0 T0 A T R F κ v₀ hcore hfw i T0 id M hMp τ ta hta hB c ((hMe c).1 hc) hMx A.μ0 A.μ0 hct y y' hyy
  obtain ⟨n, α, ys, ys', hy, hy', hk⟩ := h5
  have hZ : ConjFun (O i) (κ i) τ 1 (fun _ => 0) (fun _ => 0) := by
    have := hP τ ta hta hB 0 0 (fun h => ⟨0, 0, by simp, by rw [map_zero, map_zero]; rfl, by rw [map_zero, map_zero]; rfl⟩)
    simpa using this
  have hL := conjFun_sum (O i) (κ i) τ hZ n α
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys k) (v₀ i (sg0 D A)) g)
    (fun k g => h4.choose * ph i * R.thF i A.μ0 (ys' k) (v₀ i (sg0 D A)) g) (fun k => hP τ ta hta hB (ys k) (ys' k) (hk k))
  subst hy hy'
  convert hL using 2 with g g

  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

  · simp only [map_sum, map_smul, MultilinearMap.sum_apply, MultilinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.ConjRefTup
end
end
