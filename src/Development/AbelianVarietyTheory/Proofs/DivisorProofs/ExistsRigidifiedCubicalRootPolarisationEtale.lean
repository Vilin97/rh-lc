module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomain
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
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootLiftsFromResidueCompleteLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullEqZeroOfChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfMumfordBundleIsoUniversalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparablePointOfGeometricallyDomainStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_separable_point_of_geometrically_domain : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  first | exact @GlobalTheory.SepPoint.exists_sepPoint | exact GlobalTheory.SepPoint.exists_sepPoint | (intros; apply GlobalTheory.SepPoint.exists_sepPoint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnramifiedExtensionGroupLift

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem root_congr {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} {t t' : T ⟶ S} (e : t = t')
    (h : Root A P t) : Root A P t' := e ▸ h

theorem residue_lift (R R' k'' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] [Field k''] [Algebra (ResidueField R) k'']
    (ε : ResidueField R ⊗[R] R' ≃ₐ[ResidueField R] k'') :
    ∃ φ : k'' →+* ResidueField R', φ.comp (algebraMap (ResidueField R) k'') =
      algebraMap (ResidueField R) (ResidueField R') := by
  let g₂ : ResidueField R ⊗[R] R' →ₐ[ResidueField R] ResidueField R' :=
    Algebra.TensorProduct.lift (Algebra.ofId (ResidueField R) (ResidueField R'))
      (IsScalarTower.toAlgHom R R' (ResidueField R')) (fun _ _ => Commute.all _ _)
  refine ⟨(g₂.comp ε.symm.toAlgHom).toRingHom, ?_⟩
  ext a
  exact (g₂.comp ε.symm.toAlgHom).commutes a

end GlobalTheory.PolBundleLoc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebra

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

noncomputable section

open GlobalTheory

namespace GlobalTheory.RootFG

theorem lbIso_of_factor {Y Y' X₀ : Scheme.{0}} {M N : LB X₀} (a : Y ⟶ X₀) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀)
    (e : a' = j ≫ a) (h : LBIso (M.pull a) (N.pull a)) : LBIso (M.pull a') (N.pull a') :=
  LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h

theorem exists_fg_lbIso_of_isPullback {k : Type} [Field k] {C : Type} [CommRing C] [Algebra k C] {X : Scheme.{0}}
    (pB : X ⟶ Sp k) [QuasiCompact pB] [QuasiSeparated pB] {R₀ : Subalgebra k C} (h₀ : R₀.FG) {Y₀ Y : Scheme.{0}}
    (q₀ : Y₀ ⟶ Sp R₀) (a₀ : Y₀ ⟶ X) (hY₀ : IsPullback a₀ q₀ pB (spMap (algebraMap k R₀)))
    (y : Y ⟶ Y₀) (q : Y ⟶ Sp C) (hY : IsPullback y q q₀ (spMap R₀.val.toRingHom))
    (M N : LB Y₀) (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull y) (N.pull y)) :
    ∃ (R : Subalgebra k C) (hR : R₀ ≤ R), R.FG ∧ ∀ (Y₁ : Scheme.{0}) (q₁ : Y₁ ⟶ Sp R) (y₁ : Y₁ ⟶ Y₀),
      y₁ ≫ q₀ = q₁ ≫ spMap (Subalgebra.inclusion hR).toRingHom → LBIso (M.pull y₁) (N.pull y₁) := by
  let e : pullback pB (spMap (algebraMap k R₀)) ⟶ Y₀ :=
    hY₀.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ a₀ = pullback.fst _ _ := hY₀.lift_fst _ _ _
  have e₂ : e ≫ q₀ = pullback.snd _ _ := hY₀.lift_snd _ _ _
  let f : pullback pB (spMap (algebraMap k C)) ⟶ Y :=
    hY.lift (baseChangeMap pB R₀.val ≫ e) (pullback.snd _ _) (by
      rw [Category.assoc, e₂, baseChangeMap_snd])
  have hf : f ≫ y = baseChangeMap pB R₀.val ≫ e := hY.lift_fst _ _ _
  have H₀ : LBIso ((M.pull e).pull (baseChangeMap pB R₀.val)) ((N.pull e).pull (baseChangeMap pB R₀.val)) := by
    have := lbIso_of_factor y f _ hf.symm H
    exact LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (Spread.lbIso_pull_pull hM _ rfl).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) this
        (Spread.lbIso_pull_pull hN _ rfl))
  obtain ⟨R, hR, hRfg, H₁⟩ := exists_fg_lbIso pB h₀ (M.pull e) (N.pull e) (pull_isLB hM _) (pull_isLB hN _) H₀
  refine ⟨R, hR, hRfg, fun Y₁ q₁ y₁ w => ?_⟩
  have H₂ : LBIso (M.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e))
      (N.pull (baseChangeMap pB (Subalgebra.inclusion hR) ≫ e)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _)
      (Spread.lbIso_pull_pull hM _ rfl)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) H₁
        (Spread.lbIso_pull_pull hN _ rfl).symm)
  have hs : spMap (Subalgebra.inclusion hR).toRingHom ≫ spMap (algebraMap k R₀) = spMap (algebraMap k R) := by
    rw [spMap_comp_ring]; rfl
  let m : Y₁ ⟶ pullback pB (spMap (algebraMap k R)) :=
    pullback.lift (y₁ ≫ a₀) q₁ (by rw [Category.assoc, hY₀.w, ← Category.assoc, w, Category.assoc, hs])
  refine lbIso_of_factor _ m y₁ ?_ H₂
  apply hY₀.hom_ext
  · rw [Category.assoc, Category.assoc, e₁, baseChangeMap_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, e₂, baseChangeMap_snd, pullback.lift_snd_assoc, w]

end GlobalTheory.RootFG


open GlobalTheory GlobalTheory.RootFG in
theorem GlobalTheory.RootFG.root_fg : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left),
    P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C],
    Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  intro S A _ hA P hP k _ t C _ _ hRt
  obtain ⟨B', _, _, β, β₂, hβ, hsq, L, hL, H⟩ := hRt
  obtain ⟨A₀, _, φ₀, h₀⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h₀
  have := hA₀.proper
  have : IsProper (A₀ ⊗ A₀).hom := by
    change IsProper (pullback.fst A₀.hom A₀.hom ≫ A₀.hom)
    infer_instance

  let φ' : B'.left ⟶ A₀.left := h₀.1.lift β (B'.hom ≫ spMap (algebraMap k C)) (by rw [hβ.1.w, Category.assoc])
  have hφ'₁ : φ' ≫ φ₀ = β := h₀.1.lift_fst _ _ _
  have hφ'₂ : φ' ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k C) := h₀.1.lift_snd _ _ _
  have hB'₀ : IsGrpPullback B' A₀ (spMap (algebraMap k C)) φ' :=
    IsGrpPullback.cancel h₀ (by rw [hφ'₁]; exact hβ) hφ'₂

  obtain ⟨R₁, M, ρ, hR₁, hM, hρ₁, hρ₂, HL⟩ := GlobalTheory.LBDescent.exists_fg_lb A₀.hom B'.hom φ' hB'₀.1 L hL
  obtain ⟨B₁, _, β₁, h₁⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A₀ (spMap (algebraMap k R₁))
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ h₁
  haveI : IsCommMonObj B₁ := hB₁.comm
  let e₁ : B₁.left ⟶ pullback A₀.hom (spMap (algebraMap k R₁)) := h₁.1.isoPullback.hom
  let L₁ : LB B₁.left := M.pull e₁
  have hL₁ : L₁.IsLB := pull_isLB hM _
  let σ : Sp C ⟶ Sp R₁ := spMap R₁.val.toRingHom
  have hσ : σ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k C) := by
    rw [spMap_comp_ring]; rfl
  let ψ : B'.left ⟶ B₁.left := h₁.1.lift φ' (B'.hom ≫ σ) (by rw [hφ'₂, Category.assoc, hσ])
  have hψ₁ : ψ ≫ β₁ = φ' := h₁.1.lift_fst _ _ _
  have hψ₂ : ψ ≫ B₁.hom = B'.hom ≫ σ := h₁.1.lift_snd _ _ _
  have hψ : IsGrpPullback B' B₁ σ ψ := IsGrpPullback.cancel h₁ (by rw [hψ₁, hσ]; exact hB'₀) hψ₂
  have hρψ : ρ = ψ ≫ e₁ := by
    apply pullback.hom_ext
    · rw [hρ₁, Category.assoc, IsPullback.isoPullback_hom_fst, hψ₁]
    · rw [hρ₂, Category.assoc, IsPullback.isoPullback_hom_snd, hψ₂]
  have HL₁ : LBIso L (L₁.pull ψ) :=
    LBIso.trans hL (pull_isLB hM _) (pull_isLB hL₁ _) HL (Spread.lbIso_pull_pull hM ψ hρψ)

  have hc : IsGrpPullback B₁ A (spMap (algebraMap k R₁) ≫ t) (β₁ ≫ φ₀) := h₁.comp h₀
  let β₂₁ := (lift (pushPt hc.1.w (fst B₁ B₁)) (pushPt hc.1.w (snd B₁ B₁))).left
  have hsq₁ : IsSquare (β₁ ≫ φ₀) β₂₁ := GlobalTheory.LamPull.exists_isSquare hc.1.w
  let V := lift (pushPt hψ.1.w (fst B' B')) (pushPt hψ.1.w (snd B' B'))
  have hsqψ : IsSquare ψ V.left := GlobalTheory.LamPull.exists_isSquare hψ.1.w
  have c₁ : LBIso (abelian₂ B' L) ((abelian₂ B₁ L₁).pull V.left) :=
    GlobalTheory.SymSpread.lbIso_cube hψ hL₁ hL HL₁ (x2 B₁) (x2 B') V (fun i => by fin_cases i <;> simp [V, x2])
  have hβ₂ : β₂ = V.left ≫ β₂₁ := by
    have h' := GlobalTheory.ZM.SiegPull.isSquare_comp hsqψ hsq₁
    have eβ : ψ ≫ β₁ ≫ φ₀ = β := by rw [← Category.assoc, hψ₁, hφ'₁]
    rw [eβ] at h'
    apply pullback.hom_ext
    · exact hsq.1.trans h'.1.symm
    · exact hsq.2.trans h'.2.symm
  have hΛ₁ : (abelian₂ B₁ L₁).IsLB := LB.isLB_linComb hL₁ _ _
  have hΛ' : (abelian₂ B' L).IsLB := LB.isLB_linComb hL _ _
  have HV : LBIso ((abelian₂ B₁ L₁).pull V.left) ((P.pull β₂₁).pull V.left) :=
    LBIso.trans (pull_isLB hΛ₁ _) hΛ' (pull_isLB (pull_isLB hP _) _) c₁.symm
      (LBIso.trans hΛ' (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H (Spread.lbIso_pull_pull hP V.left hβ₂))

  obtain ⟨R₂, h₁₂, hR₂, HD⟩ := exists_fg_lbIso_of_isPullback (A₀ ⊗ A₀).hom hR₁ (B₁ ⊗ B₁).hom _
    (GlobalTheory.SymSpread.isPullback_square h₁) V.left (B' ⊗ B').hom (GlobalTheory.SymSpread.isPullback_square hψ)
    (abelian₂ B₁ L₁) (P.pull β₂₁) hΛ₁ (pull_isLB hP _) HV
  let τ : Sp R₂ ⟶ Sp R₁ := spMap (Subalgebra.inclusion h₁₂).toRingHom
  have hτ : τ ≫ spMap (algebraMap k R₁) = spMap (algebraMap k R₂) := by
    rw [spMap_comp_ring]; rfl
  obtain ⟨B₂, _, κ, hκ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback B₁ τ
  have hB₂ : IsAbelianScheme B₂ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₁ hκ
  haveI : IsCommMonObj B₂ := hB₂.comm
  refine ⟨R₂, hR₂, ?_⟩
  rw [← hτ, Category.assoc]
  let W := lift (pushPt hκ.1.w (fst B₂ B₂)) (pushPt hκ.1.w (snd B₂ B₂))
  have hsqW : IsSquare κ W.left := GlobalTheory.LamPull.exists_isSquare hκ.1.w
  have hL₂ : (L₁.pull κ).IsLB := pull_isLB hL₁ κ
  refine ⟨B₂, inferInstance, inferInstance, κ ≫ β₁ ≫ φ₀, W.left ≫ β₂₁, hκ.comp hc,
    GlobalTheory.ZM.SiegPull.isSquare_comp hsqW hsq₁, L₁.pull κ, hL₂, ?_⟩
  have d₁ : LBIso (abelian₂ B₂ (L₁.pull κ)) ((abelian₂ B₁ L₁).pull W.left) :=
    GlobalTheory.SymSpread.lbIso_cube hκ hL₁ hL₂ (lbIso_refl hL₂) (x2 B₁) (x2 B₂) W (fun i => by fin_cases i <;> simp [W, x2])
  have d₂ : LBIso ((abelian₂ B₁ L₁).pull W.left) ((P.pull β₂₁).pull W.left) :=
    HD _ (B₂ ⊗ B₂).hom W.left (GlobalTheory.SymSpread.isPullback_square hκ).w
  exact LBIso.trans (LB.isLB_linComb hL₂ _ _) (pull_isLB hΛ₁ _) (pull_isLB hP _) d₁
    (LBIso.trans (pull_isLB hΛ₁ _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) d₂
      (Spread.lbIso_pull_pull hP W.left rfl).symm)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRootExistsOverFgSubalgebraStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

theorem _root_.GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → ∀ (k : Type) [Field k] (t : Sp k ⟶ S) (C : Type) [CommRing C] [Algebra k C], Root A P (spMap (algebraMap k C) ≫ t) → ∃ B : Subalgebra k C, B.FG ∧ Root A P (spMap (algebraMap k B) ≫ t) := by
  first | exact @GlobalTheory.RootFG.root_fg | exact GlobalTheory.RootFG.root_fg | (intros; apply GlobalTheory.RootFG.root_fg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtale

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.PolBundleLocEt

open GlobalTheory.PolRoot GlobalTheory.PolBundleLoc

theorem exists_rigLB_sFam_etale :
    ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ y : Sp R ⟶ F.X, ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ρ : R →+* R'), IsAdicComplete (maximalIdeal R') R' ∧ IsLocalHom ρ ∧ Function.Injective ρ ∧ ρ.Finite ∧ ρ.Etale ∧ ∃ (B : Over (Sp R')) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A (spMap ρ ≫ y) β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro o _ ζ g n F R _ _ _ hR y
  haveI : IsAdicComplete (maximalIdeal R) R := hR
  haveI : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have hAb := F.univ.ab
  have hP := F.univ.isLB
  let k := ResidueField R
  let t₀ : Sp k ⟶ F.X := spMap (residue R) ≫ y

  have h₁ : Root F.univ.A F.univ.P (spMap (algebraMap k (AlgebraicClosure k)) ≫ t₀) :=
    root_geom F (AlgebraicClosure k) _

  obtain ⟨B, hB, h₂⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ (AlgebraicClosure k) h₁
  haveI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : Algebra.IsIntegral k B := ⟨fun b => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (Algebra.IsIntegral.isIntegral (R := k) (b : AlgebraicClosure k))⟩
  haveI : Module.Finite k B := Algebra.IsIntegral.finite

  obtain ⟨C, _, _, _, _, hC, ⟨ιC⟩, hdom⟩ := GlobalTheory.T.exists_complete_local_geomDomain' k B inferInstance
  let tC : Sp C ⟶ F.X := spMap (algebraMap k C) ≫ t₀
  have h₃ : Root F.univ.A F.univ.P (spMap (residue C) ≫ tC) := by
    refine root_congr ?_ (h₂.comp hAb (spMap ιC.toRingHom))
    simp only [tC, ← Category.assoc, spMap_comp']
    congr 2
    exact ιC.comp_algebraMap.trans (IsScalarTower.algebraMap_eq k C (ResidueField C))
  have h₄ : Root F.univ.A F.univ.P tC :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 C hC tC h₃

  obtain ⟨B', hB', h₅⟩ := GlobalTheory.T.mumfordBundleRoot_exists_over_fg_subalgebra F.X F.univ.A hAb F.univ.P hP k t₀ C h₄
  have hdom' : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B') := by
    intro K _ _ h1 h2
    haveI := hdom K h1 h2
    let m : K ⊗[k] B' →ₐ[K] K ⊗[k] C := Algebra.TensorProduct.map (AlgHom.id K K) B'.val
    have hm : Function.Injective m := by
      have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) (B'.val.toLinearMap)
        Subtype.val_injective
      exact this
    exact hm.isDomain m
  obtain ⟨k'', _, _, hfin, hsep, ⟨ψ⟩⟩ := GlobalTheory.T.exists_separable_point_of_geometrically_domain k B' ((Subalgebra.fg_iff_finiteType B').1 hB') hdom'
  have h₆ : Root F.univ.A F.univ.P (spMap (algebraMap k k'') ≫ t₀) := by
    refine root_congr ?_ (h₅.comp hAb (spMap ψ.toRingHom))
    rw [← Category.assoc, spMap_comp']
    congr 2
    exact ψ.comp_algebraMap

  haveI : Module.Finite (ResidueField R) k'' := hfin
  haveI : Algebra.IsSeparable (ResidueField R) k'' := hsep
  obtain ⟨R', _, _, hfinR, het, _, ⟨ε⟩⟩ := exists_etale_lift_of_isSeparable R k''
  haveI : HenselianLocalRing R' := henselianLocalRing_of_finite R R'
  haveI : IsLocalHom (algebraMap R R') :=
    ((local_hom_tfae (algebraMap R R')).out 1 5).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' := Algebra.FormallyUnramified.map_maximalIdeal
  have hcR' : IsAdicComplete (maximalIdeal R') R' := by
    have := isAdicComplete_map_of_finite (maximalIdeal R) R'
    rwa [hm] at this
  haveI : IsNoetherianRing R' := isNoetherian_of_tower R inferInstance
  let ρ : R →+* R' := algebraMap R R'
  obtain ⟨φ, hφ⟩ := residue_lift R R' k'' ε
  let T : Sp R' ⟶ F.X := spMap ρ ≫ y
  have h₇ : Root F.univ.A F.univ.P (spMap (residue R') ≫ T) := by
    refine root_congr ?_ (h₆.comp hAb (spMap φ))
    simp only [T, t₀, ← Category.assoc, spMap_comp']
    congr 2
    rw [← RingHom.comp_assoc, hφ]
    exact (ResidueField.map_comp_residue ρ).symm
  obtain ⟨B₁, _, _, β, β₂, hβ, hsq, L, hL, hΛ⟩ :=
    GlobalTheory.T.mumfordBundle_root_lifts_from_residue_complete_local F.X F.univ.A hAb F.univ.P hP F.univ.rig₁ F.univ.rig₂ F.princ.1 R' hcR' T h₇
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hβ
  have hP' : (F.univ.P.pull β₂).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb hP _ _
  have hker := GlobalTheory.SiegelPull.nondeg_pull hβ hsq hP hP' ((GlobalTheory.CechPic.cls_eq_iff hP' hP').1 rfl) F.princ.2
  obtain ⟨M, hM, ⟨hcub⟩⟩ := exists_rigLB_cubical R' B₁ hB₁ L hL
  have hK := GlobalTheory.KTrivOfLam.kTriv_of_lam_iso _ B₁ hB₁ (F.univ.P.pull β₂) hP' hker L hL hΛ
  have hA := GlobalTheory.T.relAmple_of_mumfordBundle_iso_universal F R' T B₁ β β₂ hβ hsq L hL hΛ
  subst hM
  have hinj : Function.Injective ρ := by
    letI : Algebra.Etale R R' := het
    haveI : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective R R'
  exact ⟨R', inferInstance, inferInstance, ρ, hcR', inferInstance, hinj, RingHom.finite_algebraMap.mpr hfinR,
    RingHom.etale_algebraMap.mpr het, B₁, inferInstance, inferInstance, β, β₂, M, hcub,
    hβ, hsq, hA, hK, hΛ⟩

end GlobalTheory.PolBundleLocEt
end
end
end
