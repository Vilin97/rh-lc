module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegralBis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNoetherianRingOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinesAtOfLatticeAtLevels
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound

-- Source module: Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.UnitsOfFieldDD

section

@[expose] public section

noncomputable section
namespace GlobalTheory.Survey.UnitsOfFieldRootsOfUnity
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

section Sum
variable {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L)

def sumEquiv (h : IsSumLat i i') : (T.V × T'.V) ≃ₗ[LL] T''.V :=
  LinearEquiv.ofBijective (i.f.coprod i'.f) h.1

theorem sumEquiv_apply (h : IsSumLat i i') (x : T.V) (y : T'.V) :
    sumEquiv i i' h (x, y) = i.f x + i'.f y := rfl

open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : _root_.Formalism.BasicNotions.LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} in
variable {T T' T'' : _root_.Formalism.BasicNotions.LocLat G Qp LL O} (i : _root_.Formalism.WeaklyAdmissibleFiltrations.LatHom T.L T''.L) (i' : _root_.Formalism.WeaklyAdmissibleFiltrations.LatHom T'.L T''.L) in
theorem _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.symm_act (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat i i') (g : G) (z : T''.V) :
    (_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm (T''.ρ g z) =
      (T.ρ g ((_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm z).1,
        T'.ρ g ((_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm z).2) := by
  apply (_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).injective
  rw [LinearEquiv.apply_symm_apply, _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv_apply, i.equiv, i'.equiv, ← map_add (f := _),
    ← _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv_apply i i' h, Prod.mk.eta, LinearEquiv.apply_symm_apply]

def pr₁ (h : IsSumLat i i') : LatHom T''.L T.L where
  f := LinearMap.fst LL _ _ ∘ₗ (sumEquiv i i' h).symm.toLinearMap
  equiv := fun g z => by simp [symm_act]
  cont := by
    have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
    exact IsModuleTopology.continuous_of_linearMap _
  T_le := fun z hz => by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.2 z hz
    rw [← sumEquiv_apply i i' h]
    simpa using hx

def pr₂ (h : IsSumLat i i') : LatHom T''.L T'.L where
  f := LinearMap.snd LL _ _ ∘ₗ (sumEquiv i i' h).symm.toLinearMap
  equiv := fun g z => by simp [symm_act]
  cont := by
    have : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
    exact IsModuleTopology.continuous_of_linearMap _
  T_le := fun z hz => by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.2 z hz
    rw [← sumEquiv_apply i i' h]
    simpa using hy

end Sum

theorem latHom_ext {T T' : LocLat G Qp LL O} {f g : LatHom T.L T'.L} (h : ∀ x, f.f x = g.f x) :
    f = g := by
  cases f; cases g
  congr 1
  exact LinearMap.ext h

theorem map_of_zero {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (h : ∀ x, f.f x = 0)
    (x : W.DD T) : W.map f x = 0 := by
  have : f = latComp (latSmul T' (0 : O)) f := latHom_ext fun y => by
    simp [latComp, latSmul, h]
  rw [this, W.map_comp, W.map_latSmul, zero_smul]

theorem sum_N {T T' T'' : LocLat G Qp LL O} (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (hT'' : IsCrys PD T''.ρ)
    (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) (h : IsSumLat i i') (x : W.DD T) (y : W.DD T') :
    W.map i x + W.map i' y ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T') := by
  have e1 : ∀ a, (pr₁ i i' h).f (i.f a) = a := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (a, 0)
    rw [sumEquiv_apply, map_zero, add_zero] at this
    simp [pr₁, this]
  have e2 : ∀ a, (pr₁ i i' h).f (i'.f a) = 0 := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (0, a)
    rw [sumEquiv_apply, map_zero, zero_add] at this
    simp [pr₁, this]
  have e3 : ∀ a, (pr₂ i i' h).f (i.f a) = 0 := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (a, 0)
    rw [sumEquiv_apply, map_zero, add_zero] at this
    simp [pr₂, this]
  have e4 : ∀ a, (pr₂ i i' h).f (i'.f a) = a := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (0, a)
    rw [sumEquiv_apply, map_zero, zero_add] at this
    simp [pr₂, this]
  constructor
  · intro hz
    have h1 := W.map_N (pr₁ i i' h) hT'' hT _ hz
    have h2 := W.map_N (pr₂ i i' h) hT'' hT' _ hz
    rw [map_add (f := _), ← W.map_comp, ← W.map_comp] at h1 h2
    rw [show latComp (pr₁ i i' h) i = latId T from latHom_ext e1, W.map_id,
      map_of_zero (latComp (pr₁ i i' h) i') e2, add_zero] at h1
    rw [show latComp (pr₂ i i' h) i' = latId T' from latHom_ext e4, W.map_id,
      map_of_zero (latComp (pr₂ i i' h) i) e3, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hx, hy⟩
    exact (W.N T'').add_mem (W.map_N i hT hT'' x hx) (W.map_N i' hT' hT'' y hy)

theorem sumFor_of_crys
    (hc : ∀ (T T' T'' : LocLat G Qp LL O) (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L),
      IsSumLat i i' → IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ) : SumFor W := by
  intro T T' T'' hT hT' i i' h
  have key : ∀ a b, (pr₁ i i' h).f (i.f a + i'.f b) = a ∧ (pr₂ i i' h).f (i.f a + i'.f b) = b :=
    fun a b => by
      have := (sumEquiv i i' h).symm_apply_apply (a, b)
      rw [sumEquiv_apply] at this
      simp only [pr₁, pr₂, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
      simp
  have hbij : Function.Bijective ((W.map i).coprod (W.map i')) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨x, y⟩ hxy
      simp only [LinearMap.coprod_apply] at hxy
      have h1 := congrArg (W.map (pr₁ i i' h)) hxy
      have h2 := congrArg (W.map (pr₂ i i' h)) hxy
      rw [map_add (f := _), ← W.map_comp, ← W.map_comp, map_zero] at h1 h2
      rw [show latComp (pr₁ i i' h) i = latId T from latHom_ext fun a => by
          simpa [latComp, latId] using (key a 0).1, W.map_id,
        map_of_zero (latComp (pr₁ i i' h) i') (fun a => by simpa [latComp] using (key 0 a).1),
        add_zero] at h1
      rw [show latComp (pr₂ i i' h) i' = latId T' from latHom_ext fun a => by
          simpa [latComp, latId] using (key 0 a).2, W.map_id,
        map_of_zero (latComp (pr₂ i i' h) i) (fun a => by simpa [latComp] using (key a 0).2),
        zero_add] at h2
      simp [h1, h2]
    · intro z
      refine ⟨(W.map (pr₁ i i' h) z, W.map (pr₂ i i' h) z), ?_⟩
      simp only [LinearMap.coprod_apply]
      rw [← W.map_comp, ← W.map_comp, ← W.map_latAdd,
        show latAdd (latComp i (pr₁ i i' h)) (latComp i' (pr₂ i i' h)) = latId T'' from
          latHom_ext fun a => by
            obtain ⟨⟨x, y⟩, rfl⟩ := (sumEquiv i i' h).surjective a
            rw [sumEquiv_apply]
            change i.f ((pr₁ i i' h).f _) + i'.f ((pr₂ i i' h).f _) = _
            rw [(key x y).1, (key x y).2]
            rfl, W.map_id]
  refine ⟨LinearEquiv.ofBijective _ hbij, fun x y => rfl, fun x y => ?_, fun g x y => ?_,
    fun x y => sum_N hT hT' (hc T T' T'' i i' h hT hT') i i' h x y⟩
  · change W.φD T'' (W.map i x + W.map i' y) = W.map i _ + W.map i' _
    rw [map_add (f := _), ← W.map_φ, ← W.map_φ]
    rfl
  · change W.γD T'' g (W.map i x + W.map i' y) = W.map i _ + W.map i' _
    rw [map_add (f := _), ← W.map_γ, ← W.map_γ]
    rfl

end GlobalTheory.Survey.UnitsOfFieldRootsOfUnity
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart

section

@[expose] public section

namespace GlobalTheory.WachSum

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem sumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumPart l P H := by
  intro K s LL h
  exact GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumFor_of_crys fun _ _ _ i i' hs hT hT' =>
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_isSumLat i i' hT hT' hs

end GlobalTheory.WachSum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveOfSumFor

section

@[expose] public section

namespace GlobalTheory.WachUse

open GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}

theorem additive_of_sumFor (hW : GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor W) : Additive W := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumFor at hW
  intro T T' S f g hT hT' hb hs z hz
  obtain ⟨σ, hσ, -, -, hmem⟩ := hW T T' S hT hT' f g (by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat
    exact ⟨hb, hs⟩)

  set p := σ.symm z with hp
  have hz' : σ (p.1, p.2) = z := by simp [hp]
  rw [← hz'] at hz
  obtain ⟨hx, hy⟩ := (hmem p.1 p.2).1 hz
  exact ⟨p.1, hx, p.2, hy, by rw [← hz', hσ]⟩

end Generic

theorem additive_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P)
    (E : LocFon l P AI H) (C : LocCmpT l P AI H E), ∀ (K LL : FinExt l) (h : CaseA K LL),
    Additive (H.W K 1 LL h.2.2) := by
  intro l _ P _ H _ _ K LL h

  exact additive_of_sumFor (GlobalTheory.WachSum.sumPart l P H K 1 LL h.2.2)

end GlobalTheory.WachUse
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmitted

section

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

noncomputable section

namespace GlobalTheory.WachQN

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem invBasis_of_basisModule [Nontrivial O] (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {π' : LetA O n}
    (h : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') :
    ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, (∀ j, b j ∈ W.NΔ T) ∧ LinearIndependent (LetA O n) b ∧
      W.N T = Submodule.span (LetA O n) (Set.range b) := by
  obtain ⟨⟨r, b, hbN, huniq, -⟩, -⟩ := h
  obtain ⟨a0, -, ha0⟩ := huniq 0 (W.N T).zero_mem
  have hli : LinearIndependent (LetA O n) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    exact congrFun ((ha0 g hg.symm).trans (ha0 0 (by simp)).symm) j
  have hsp : W.N T = Submodule.span (LetA O n) (Set.range b) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hbN j).1))
    obtain ⟨a, ha, -⟩ := huniq x hx
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr : r = Module.finrank O ↥T.L.T := by
    let bN := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hbc := W.N_base T hT
    let bD := (Algebra.TensorProduct.basis W.EE bN).map hbc.equiv
    haveI : Nontrivial W.EE := W.EE_inj.nontrivial
    rw [← (W.DD_free T).2, Module.finrank_eq_card_basis bD, Fintype.card_fin]
  subst hr
  exact ⟨b, hbN, hli, hsp⟩

end Generic

theorem invBasis_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.InvBasis ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h9 l _ K LL hA T hT
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hfr : Module.finrank ↥(K0 K) ↥K.1 = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap ↥(K0 K) ↥K.1) hbij).finrank_eq.symm.trans (Module.finrank_self _)
  exact invBasis_of_basisModule _ T hT ((h9 l K 1 LL hA.2.2 T hT ((HW l).W_s K 1 LL hA.2.2)
    (by rw [(D.loc l).PD_p]; exact hA.2.1)).2.2 hfr).2

theorem heights_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.Heights ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h5 l _ K LL hA T U M hh hU hb i
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
  have hJ := GlobalTheory.WachUse.HeightsProof.jumpsOverLetters_of_crysWith _ T U M hh hU hb
  have hp := h5 l K 1 LL hA.2.2 T M hh hU.1
    (fun τ j hτ => hJ j τ (fun c => by simpa using congrArg (fun f => f c) hτ))
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [← GlobalTheory.WachUse.HeightsProof.φD_letE]
    exact hp.1 i _ ⟨x, hx, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (GlobalTheory.WachUse.HeightsProof.Nl_le _ T (i - 1)))
      (hp.2.1 i _ ⟨y, hy, rfl⟩)

theorem saturated_caseA (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) :
    GlobalTheory.WachUse.Saturated ((HW l).W K 1 LL hA.2.2) := by
  intro T' T f hT hb x hx
  have hT' : IsCrys ((D.loc l).PD K) T'.ρ :=
    GlobalTheory.HTW.Rec.isCrys_of_equiv ((D.loc l).PD K) (LinearEquiv.ofBijective f.f hb) f.equiv hT
  exact ((GlobalTheory.NL.Isog.isog_loc (HW l) K 1 LL hA.2.2 T' T f hT' hT hb).2.2 x).1 hx

theorem qN_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm h l _ K LL hA
  have hI := invBasis_of_admitted D HW F h.2.2.2.2.2.2.2.2.1 l K LL hA
  have hS := GlobalTheory.SenOperator.senOp_of_record D HW F Cm l K LL hA
  exact ⟨hI, heights_of_admitted D HW F h.2.2.2.2.1 l K LL hA,
    GlobalTheory.WachRankOne.rankOne_of_senOp (D.locA l) (HW l) (F l) (Cm l) K LL hA hI hS,
    saturated_caseA D HW l K LL hA,
    GlobalTheory.WachUse.additive_of_caseA (D.locA l) (HW l) (F l) (Cm l) K LL hA, hS⟩

end GlobalTheory.WachQN
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmittedStatement

section

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem _root_.GlobalTheory.T.wachLattice_usedProperties_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachQN.qN_of_admitted | exact GlobalTheory.WachQN.qN_of_admitted | (intros; apply GlobalTheory.WachQN.qN_of_admitted <;> assumption)
end
end
