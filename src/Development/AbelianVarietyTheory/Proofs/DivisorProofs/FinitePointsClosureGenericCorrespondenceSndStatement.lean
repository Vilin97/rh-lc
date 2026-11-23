module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenySourcesAtCharPPointStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimit

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ClosedPtIsog

theorem charP_of_notMem_basicOpen {X : Scheme.{0}} {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (h : Sp k ⟶ X)
    (hz : h (IsLocalRing.closedPoint k) ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) : CharP k p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  by_contra hne
  apply hz
  have hu : IsUnit ((p : ℕ) : Γ(Sp k, h ⁻¹ᵁ ⊤)) := by
    have := (IsUnit.mk0 _ hne).map
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.map (homOfLE (le_top (a := h ⁻¹ᵁ ⊤))).op).hom)
    rwa [map_natCast] at this
  have hm : IsLocalRing.closedPoint k ∈ h ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hm

theorem exists_isPIsog_closedPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  intro p _ D R _ _ _ _ b N hN hNp _ c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz u hu
  obtain ⟨V, K, _, _, _, _, _, _, y', z', x, hy, hz', hyu, hzz⟩ := hu
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V K
  have hyz : y' ≫ M.s = z' ≫ M.s :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant (Spec.map (CommRingCat.ofHom (Int.castRingHom R))) (specZIsTerminal.hom_ext _ _)
      (spMap (algebraMap V K)) (by rw [reassoc_of% hy, reassoc_of% hz', hst])
  have pull : ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (f : S' ⟶ S) (σ : S' ⟶ Sp R), f ≫ s = σ →
      ∃ o₁ : Obj b N σ, Nonempty (ObjMap o₁ o f) := by
    rintro S S' s o f σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N S S' s f o
  have objMapComp : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
      {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃}
      {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}, ObjMap o₁ o₂ f → ObjMap o₂ o₃ g →
      ObjMap o₁ o₃ (f ≫ g) := by
    intro S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₁ m₂
    exact {
      φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := IsGrpPullback.comp m₁.cart m₂.cart
      sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
        by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
        (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂)
          (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
          m₂.pol)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  obtain ⟨oV, ⟨mV⟩⟩ := pull M.univ y' (z' ≫ M.s) hyz
  obtain ⟨oV', ⟨mV'⟩⟩ := pull M.univ z' (z' ≫ M.s) rfl
  obtain ⟨oK, ⟨nK⟩⟩ := pull o₀ x _ rfl
  obtain ⟨oK', ⟨nK'⟩⟩ := pull o₀' x _ rfl
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ x o₀ o₀' oK oK' nK nK' ψ₀ hψ
  have m₁ : ObjMap oK M.univ (spMap (algebraMap V K) ≫ y') := hy ▸ objMapComp nK ms₀
  have m₁' : ObjMap oK' M.univ (spMap (algebraMap V K) ≫ z') := hz' ▸ objMapComp nK' mt₀
  obtain ⟨n₁, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁ mV
  obtain ⟨n₁', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁' mV'
  obtain ⟨e, he⟩ := hψ.exists_eq_pow
  have hdom : IsDominant (spMap (algebraMap V K)) := inferInstance
  obtain ⟨ψV, hψV, -⟩ := PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨e, he, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V K)) _ (z' ≫ M.s)
    (GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V K) hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2)
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).1) oV oV' oK oK' n₁ n₁' ψK hψK
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  let g : Sp k ⟶ Sp V := spMap φ
  have hg : g (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint φ
  have hζ : (g ≫ z') (IsLocalRing.closedPoint k) = z :=
    (Scheme.Hom.comp_apply g z' _).trans ((congrArg z' hg).trans hzz)
  have hυ : (g ≫ y') (IsLocalRing.closedPoint k) = u :=
    (Scheme.Hom.comp_apply g y' _).trans ((congrArg y' hg).trans hyu)
  obtain ⟨ou, ⟨nu⟩⟩ := pull oV g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨oz, ⟨nz⟩⟩ := pull oV' g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨ψk, hψk, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ g oV oV' ou oz nu nz ψV hψV
  exact ⟨k, inferInstance, inferInstance, charP_of_notMem_basicOpen Fact.out (g ≫ z') (hζ ▸ hz), g ≫ z', g ≫ y', ou, oz,
    objMapComp nu mV, objMapComp nz mV', ψk,
    by rw [Category.assoc, Category.assoc, hyz], hψk, hζ, hυ⟩

end GlobalTheory.UPel.HT.ES.ClosedPtIsog
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  first | (exact @GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (exact GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint) | (intros; apply GlobalTheory.UPel.HT.ES.ClosedPtIsog.exists_isPIsog_closedPoint  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSnd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem finite_dvr_limits_of_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X)
    (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt →
    ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀),
      spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧
      y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro X Y₀ S q U s₀ t₀ gt hq hS _ hgt hfin z hz
  refine ((gt.finite_preimage_singleton ⟨z, hz⟩).image s₀).subset ?_
  rintro u ⟨V, K, _, _, _, _, _, _, y', z', x, h1, h2, rfl, rfl⟩

  have hr : Set.range z' ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint w).map z'.continuous).mem_open U.isOpen hz
  set z'' := IsOpenImmersion.lift U.ι z' hr with hz''
  have hfac : z'' ≫ U.ι = z' := IsOpenImmersion.lift_fac _ _ _

  have hsq : x ≫ gt = spMap (algebraMap V K) ≫ z'' := by
    rw [← cancel_mono U.ι, Category.assoc, hgt, Category.assoc, hfac, h2]
  have hE : ValuativeCriterion.Existence gt :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed gt) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) gt).1
  obtain ⟨l, hl1, hl2⟩ := (hE { R := V, K := K, i₁ := x, i₂ := z'', commSq := ⟨hsq⟩ }).exists_lift
  dsimp only at hl1 hl2

  have hU := IsSeparated.valuativeCriterion (q ≫ terminal.from S)
  have hsq' : (x ≫ s₀) ≫ (q ≫ terminal.from S) = spMap (algebraMap V K) ≫ terminal.from _ :=
    terminal.hom_ext _ _
  have hy : y' = l ≫ s₀ := by
    have := hU { R := V, K := K, i₁ := x ≫ s₀, i₂ := terminal.from _, commSq := ⟨hsq'⟩ }
    have e := this.elim ⟨y', h1, terminal.hom_ext _ _⟩
      ⟨l ≫ s₀, by change spMap (algebraMap V K) ≫ l ≫ s₀ = x ≫ s₀; rw [← Category.assoc, hl1], terminal.hom_ext _ _⟩
    exact congrArg CommSq.LiftStruct.l e
  refine ⟨l (IsLocalRing.closedPoint V), ?_, ?_⟩
  · show gt (l _) = _
    apply Subtype.ext
    change (l ≫ gt ≫ U.ι) _ = z' _
    rw [← Category.assoc, hl2, hfac]
  · rw [hy]; rfl

end GlobalTheory.UPel.HT.ES
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSndStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X) (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt → ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSnd

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  intro p _ D R _ _ _ _ b N hN hNp hpR r w j c hw hu hj hc hm M Y₀ s₀ t₀ gs gt o₀ o₀' ms₀ mt₀ ψ₀ hst hgs hgt _ _ hgtf _ hψ _ z
  by_cases hz : z ∈ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))
  · exact GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd M.X Y₀ (Sp R) M.s _ s₀ t₀ gt (GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj) inferInstance hst hgt
      hgtf z hz
  · exact (GlobalTheory.T.finite_pIsogenySources_at_charP_point p D R b N hN hNp hpR c hm M z).subset
      (GlobalTheory.T.exists_pIsogeny_at_closedPoint_of_dvr_limit p D R b N hN hNp hpR c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsClosureGenericCorrespondenceSndStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_points_closure_genericCorrespondence_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd <;> assumption)
end
end
