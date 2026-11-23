module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationExistsIsComplStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationIsotropicOfSkewStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationLieOfMapIntoHodgeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoords
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
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLiftLieOfHodgeSummandLieStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPrimeToPLevelLiftSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationPushforwardMem

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

theorem push_constMor_pull {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀)
    [IsMonHom g] (c : primDR A₀) :
    primPull (epsDP k) (GlobalTheory.DeRham.epsRed k) g ((constMor A₀).pull c) =
      (constMor A₀).pull (primPull (dp0 k) (𝟙 _) g c) := by
  have K := (constMor A₀).isMor.comp (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor
  apply Subtype.ext
  exact (IsMor.pullback1_comp (constMor A₀).isMor
    (homMor (epsDP k) (GlobalTheory.DeRham.epsRed k) g).isMor K (fun _ ↦ rfl) rfl c.1).trans
    (IsMor.pullback1_comp (homMor (dp0 k) (𝟙 _) g).isMor (constMor A₀).isMor K
      (fun _ ↦ rfl) (by simp) c.1).symm

theorem push_mem_graphFil : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (f : HdR A₀ →ₗ[k] HdR A₀), (∀ x ∈ Fil A₀, f (push (dp0 k) (𝟙 _) g x) - push (dp0 k) (𝟙 _) g (f x) ∈ Fil A₀) → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ∈ GlobalTheory.HTRealise.graphFil A₀ f := by
  intro k _ A₀ _ g _ f hf d hd
  obtain ⟨x, hx, y, hy, e⟩ := hd
  refine ⟨push (dp0 k) (𝟙 _) g x, push_mem_Fil g hx,
    push (dp0 k) (𝟙 _) g (f x) - f (push (dp0 k) (𝟙 _) g x) + push (dp0 k) (𝟙 _) g y,
    add_mem (by rw [← neg_sub]; exact neg_mem (hf x hx)) (push_mem_Fil g hy), fun c ↦ ?_⟩
  rw [push_apply, push_constMor_pull, e]
  simp only [push_apply, LinearMap.add_apply, LinearMap.sub_apply]
  congr 2
  ring

end GlobalTheory.HTRealise
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberGraphFiltrationPushforwardMemStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.dualNumberGraphFiltration_pushforward_mem : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (g : A₀ ⟶ A₀) [IsMonHom g] (f : HdR A₀ →ₗ[k] HdR A₀), (∀ x ∈ Fil A₀, f (push (dp0 k) (𝟙 _) g x) - push (dp0 k) (𝟙 _) g (f x) ∈ Fil A₀) → ∀ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, push (epsDP k) (GlobalTheory.DeRham.epsRed k) g d ∈ GlobalTheory.HTRealise.graphFil A₀ f := by
  first | exact @GlobalTheory.HTRealise.push_mem_graphFil | exact GlobalTheory.HTRealise.push_mem_graphFil | (intros; apply GlobalTheory.HTRealise.push_mem_graphFil <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceLeHodgeFiltrationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (β : R →+* k) (s : Sp k ⟶ Sp R), s = spMap β → ∀ o₀ : GlobalTheory.UPel.HT.Obj b N s, GlobalTheory.HTCount.lieZ o₀ β ≤ Fil o₀.A := by
  first | (exact @GlobalTheory.HTCount.lieZ_le_Fil) | (exact GlobalTheory.HTCount.lieZ_le_Fil) | (intros; apply GlobalTheory.HTCount.lieZ_le_Fil  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReduction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

variable {k : Type} [Field k]

theorem crysRed_pull_constMor_pull (A₀ : Over (Sp k)) [GrpObj A₀] (c : primDR A₀) :
    (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).pull ((constMor A₀).pull c) = c := by
  rw [GrpMor.pull_pull (constMor A₀) (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀)
    (homMor (dp0 k) (𝟙 _) (𝟙 A₀)) (fun _ ↦ rfl) (by simp) c]
  exact Subtype.ext (IsMor.pullCohomologyOne_id _ c.1)



theorem mem_Fil_iff_exists_graphFil_corr (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀) :
    y ∈ Fil A₀ ↔ ∃ d ∈ graphFil A₀ f,
      (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  constructor
  · intro hy
    obtain ⟨d, hd⟩ := exists_crys hA y (f y)
    refine ⟨d, ⟨y, hy, 0, zero_mem _, fun c ↦ by rw [hd c]; simp⟩, fun c ↦ ?_⟩
    obtain ⟨z, rfl⟩ := (isBC_constMor hA).2 c
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TrivSqZeroExt.fst_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, TrivSqZeroExt.fst_add]
    | tmul a c =>
      rw [liftSemi_tmul, map_smulₛₗ, map_smul, crysRed_pull_constMor_pull, map_smul, hd c]
      simp
  · rintro ⟨d, ⟨x, hx, y', -, e⟩, hc⟩
    have : y = x := LinearMap.ext fun c ↦ by
      have h1 := hc ((constMor A₀).pull c)
      rw [crysRed_pull_constMor_pull, e c] at h1
      simpa using h1
    exact this ▸ hx

end GlobalTheory.HTRealise
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffDualNumberGraphReductionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (y : HdR A₀), y ∈ Fil A₀ ↔ ∃ d ∈ GlobalTheory.HTRealise.graphFil A₀ f, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (epsDP k) rfl A₀).Corr d y := by
  first | (exact @GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr) | (exact GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr) | (intros; apply GlobalTheory.HTRealise.mem_Fil_iff_exists_graphFil_corr  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

private theorem isFilLift_of_graphFil {k : Type} [Field k]
    {A₀ : Over (Sp k)} [GrpObj A₀] {A : Over (Sp (DualNumber k))} [GrpObj A]
    {i : A₀.left ⟶ A.left} (h : IsGrpPullback A₀ A (GlobalTheory.DeRham.epsRed k) i)
    (hA₀ : IsAbelianScheme A₀) (f : HdR A₀ →ₗ[k] HdR A₀)
    (hE : liftFil (epsDP k) h = graphFil A₀ f)
    (x : HdR A₀) (hx : x ∈ Fil A₀) : IsFilLift h x (f x) := by
  obtain ⟨d, hd⟩ := @exists_crys k _ A₀ _ hA₀ x (f x)
  have hGraph := (@mem_graphFil k _ A₀ _ f d).2
    ⟨x, hx, 0, zero_mem _, fun c => by simpa only [LinearMap.zero_apply, add_zero] using hd c⟩
  exact ⟨d, hE.symm ▸ hGraph, hd⟩

-- Keep the divided powers abstract so the dual-number graph lemmas can supply the hypotheses directly.
private theorem lift_with_filtration
    (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p)
    (C k : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k]
    (π : C →+* k) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C)
    (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR))
    (κ : DividedPowers (RingHom.ker π)) (hκ : κ = divided₂ hsq)
    (E : Submodule C (Crys κ (spMap π) o₀.A)) (hCompl : ∃ M, IsCompl E M)
    (hReduction : ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔
      ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (π := π) κ rfl o₀.A).Corr d y)
    (hStable : ∀ (c : D.O) d, d ∈ E →
      (haveI := o₀.act.hom c; push κ (spMap π) (o₀.act.act c) d) ∈ E)
    (hIsotropic : ∀ φ' : LinearMap.BilinForm C (Crys κ (spMap π) o₀.A),
      GlobalTheory.AbDual.IsCorrForm κ (spMap π) o₀.A o₀.A o₀.P φ' →
        ∀ x ∈ E, ∀ y ∈ E, φ' x y = 0)
    (hLie : ∀ d : Crys κ (spMap π) o₀.A,
      (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
        push κ (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d) - tR b.ρ • d ∈ E →
      ∃ w : Fin D.a → Crys κ (spMap π) o₀.A,
        (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
          push κ (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i))
            - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap π)),
      liftFil κ m'.cart = E := by
  subst κ
  obtain ⟨A, grp, i, h, act, hA, hE, hact⟩ :=
    GlobalTheory.HTDeform.exists_lift_oAct p D R b N C k π hπ hsq tR o₀ E hCompl hReduction hStable
  have hComm : IsCommMonObj A := hA.comm
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C k π hπ hsq tR o₀ A i h
      hA act hact (fun φ' hφ' x hx y hy => hIsotropic φ' hφ' x (hE ▸ hx) y (hE ▸ hy))
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ :=
    GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C k π hπ hsq tR o₀ A i h hA
      act hact hN P φ₂ hP hsq2 hpol
  rw [← hE] at hLie
  let o' : GlobalTheory.UPel.HT.Obj b N (spMap tR) :=
    { A := A
      grp := grp
      comm := hComm
      ab := hA
      act := act
      P := P
      isLB := hP
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hker
      rosati := hros
      lie := GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C k
        π hπ hsq tR o₀ A i h hA act hact hLie
      lieRank := GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift p D R b N C k
        π hπ hsq tR o₀ A i h act hact
      eta := eta
      eta_add := e1
      eta_lin := e2
      eta_ker := e3
      geom := e4 }
  let m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap π) :=
    { φ := i, φ₂ := φ₂, cart := h, sq := hsq2, act := hact, pol := hpol, eta := e5 }
  exact ⟨o', m', hE⟩

theorem realise_core (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p) (k : Type) [Field k] (β : R →+* k)
    (s : Sp k ⟶ Sp R) (hs : s = spMap β) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ : LinearMap.BilinForm k (HdR o₀.A)) (hφ : GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ)
    (f : HdR o₀.A →ₗ[k] HdR o₀.A)
    (hf : IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f)
    (tR : R →+* DualNumber k) (htR : tR = (algebraMap k (DualNumber k)).comp β)
    (hs' : s = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap tR) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  subst tR
  subst hs'
  let tR := (algebraMap k (DualNumber k)).comp β
  have hZ := GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration p D R b N k β _ hs o₀
  have : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  have : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k (DualNumber k)
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have hA₀ := o₀.ab
  have hCompl := @GlobalTheory.T.dualNumberGraphFiltration_exists_isCompl k _ o₀.A o₀.grp hA₀ f
  have hReduction := @GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction k _ o₀.A o₀.grp hA₀ f
  have hStable (c : D.O) := @GlobalTheory.T.dualNumberGraphFiltration_pushforward_mem
    k _ o₀.A o₀.grp (o₀.act.act c) (o₀.act.hom c) f (hf.1 c)
  have hIsotropic := @GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew
    k _ o₀.A o₀.grp hA₀ o₀.P o₀.isLB φ hφ f hf.2.2
  have hLie := GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge p D R b N k β _ o₀ f hZ hf.2.1
  obtain ⟨o', m', hE⟩ := lift_with_filtration p D R b N hN (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ (SqExt.dual k).sq tR o₀ (epsDP k) rfl (graphFil o₀.A f)
    hCompl hReduction hStable hIsotropic hLie
  exact ⟨o', m', @isFilLift_of_graphFil k _ o₀.A o₀.grp o'.A o'.grp m'.φ m'.cart hA₀ f hE⟩

end GlobalTheory.HTRealise

theorem GlobalTheory.UPel.HT.realise_isKS : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N _ hN k _ _ t o₀ β ht φ hφ f hf
  have e1 : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have e2 : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun r => rfl)
  rw [e1]
  exact GlobalTheory.HTRealise.realise_core p D R b N hN k β t ht o₀ φ hφ f hf _ rfl e2
end
end
end
