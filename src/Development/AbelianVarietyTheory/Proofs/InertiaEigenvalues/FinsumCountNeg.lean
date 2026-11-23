module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStableLatticeModIrreducibleEqBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveMaxUnramifiedSubfieldAlgebraMap

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TopSteps.FinSummandDim

open Module TensorProduct
open GlobalTheory.AdmLoc GlobalTheory.TopSteps GlobalTheory.TopSteps.FinSummand Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace Qp] [TopologicalSpace LL]

theorem h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) : H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ = ⊥ := by
  obtain ⟨_, _, _⟩ := hO.1
  refine invariants_stableLattice_mod_irreducible_eq_bot (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hlam ?_
  change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
  rw [latRep_twLattice]
  exact h0

theorem finrank_h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) :
    finrank LL ↥(H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) = 0 := by
  rw [h0V_tw hO Γ hχ hlam h0, finrank_bot]

theorem isCompl_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    ∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C := by
  obtain ⟨_, _, _⟩ := hO.1
  exact exists_isCompl_of_saturated _ (h1fT_saturated PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L)

theorem finrank_tw [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V)) :
    finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = finrank LL (FiniteCohomology PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) := by
  obtain ⟨_, _, _⟩ := hO.1
  exact finrank_h1fT PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hT

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem cont_inv (hC : S.CrysCalc) : Continuous fun g => algebraMap S.O ↥S.LL.1 (S.Γ.χ₁⁻¹ g) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2.1

abbrev tw (hC : S.CrysCalc) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O := twLat S.Γ.T₀ S.Γ.χ₁⁻¹ (cont_inv S hC)

theorem tw_crysWith (hC : S.CrysCalc) :
    CrysWith (P.PD S.K) S.emb (tw S hC).ρ (fun i => (S.D.U i).map (· + -S.D.w i)) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1

set_option synthInstance.maxHeartbeats 100000 in
theorem tw_finrank_h0V (hC : S.CrysCalc) (hV : S.Vanish) : finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) = 0 := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact finrank_h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

theorem exists_isCompl (hC : S.CrysCalc) (hH : S.FreeH) :
    ∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C :=
  isCompl_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hH.1.2.1

theorem finrank_hf (hC : S.CrysCalc) :
    finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) :=
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  finrank_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC)
    (GlobalTheory.Cyc.locLat_isOpen (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ.T₀)

theorem sum_card_neg :
    ∑ i, Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) = S.D.dsum := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

theorem bijective_maxUnramifiedSubfield_algebraMap : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) := by
  obtain ⟨⟨-, hA, -⟩, -⟩ := S.hyp
  exact ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩

theorem fSummand_of_finrank (hC : S.CrysCalc) (hH : S.FreeH)
    (hd : finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) = S.D.dsum) : S.FSummand :=
  ⟨exists_isCompl S hC hH, (finrank_hf S hC).trans hd⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem fSummand_of_dim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ)) : S.FSummand := by
  refine fSummand_of_finrank S hC hH ?_
  have h0 := tw_finrank_h0V S hC hV
  have h1 : ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ) = (S.D.dsum : ℤ) := by
    rw [← sum_card_neg S, Nat.cast_sum]
  have key : ∀ (a b c : ℕ) (s : ℤ), (a : ℤ) = (b : ℤ) + s → b = 0 → s = (c : ℤ) → a = c := by
    intro a b c s h h' h''
    omega
  exact key _ _ _ _ hd h0 h1

end GlobalTheory.TopSteps.FinSummandDim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCountNeg

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TopSteps.FinSummandJumps

open Module

theorem finsum_count_neg (U : Multiset ℤ) (m : ℤ → ℤ) (h : ∀ a, m a = (U.count a : ℤ)) :
    ∑ᶠ (a : ℤ) (_ : a < 0), m a = (Multiset.card (U.filter (· < 0)) : ℤ) := by
  classical
  have h1 : ∀ a : ℤ, ∑ᶠ (_ : a < 0), m a = (((U.filter (· < 0)).count a : ℕ) : ℤ) := fun a => by
    rw [finsum_eq_if, h, Multiset.count_filter]
    split_ifs <;> simp
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := (U.filter (· < 0)).toFinset),
    ← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
  intro a ha
  have ha' : (U.filter (· < 0)).count a ≠ 0 := fun h0 => ha (by simp only [h0, Nat.cast_zero])
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha'))

section General

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

theorem finsum_multV_neg {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (U : ZMod n → Multiset ℤ)
    (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    ∑ᶠ (τ : K →ₐ[Qp] LL), ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => finsum_count_neg (U i) _ (hU i (e i) (he i))

end General


open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.TopSteps.FinSummandDim in
theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), tableLineDegreeTwo.BlochKatoJumpDimension (P.PD S.K) (LL := ↥S.LL.1) (O := S.O) (IK S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P S hB hC hV hH
  obtain ⟨⟨-, -, -, hemb, -⟩, -⟩ := S.hyp
  have : IsTopologicalAddGroup (tw S hC).V := IsModuleTopology.topologicalAddGroup ↥S.LL.1 (tw S hC).V
  have h := hB.1 (tw S hC).V (tw S hC).ρ (tw S hC).cont (tw_crysWith S hC).1
  exact fSummand_of_dim S hC hV hH (h.trans (congrArg _
    (finsum_multV_neg (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandJumps
end
end
end
