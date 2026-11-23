module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRoot
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymFrameClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitSectionIntegralExpansionMemRangeInverseExpaStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfUniformisationOverDvr

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_expandsF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  intro R _ _ I hI hC D A G _ _ U hG F _ _ _ N hN w₀ hw₀ lab hlab
  haveI := hC
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have gf : GlobalFnsSt := hL.1.globalFns
  have hN1 : 1 ≤ N := hN.pos
  obtain ⟨hbij, hlin⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨b₁, b₂⟩ := hbij F N hN1 w₀ hw₀
  choose E hE using fun s => (b₂ s).exists
  obtain ⟨f, hf, hfN⟩ := GlobalTheory.TorsionIso.torsion_clause R I hI D A G hG U F N hN1
  have hlabf : ∀ p, lab p = f p := fun p => (hf.1 p (lab p)).1 (hlab p)
  have hSF := GlobalTheory.SymFrameClause.symFrame_clause R I hI D A G hG U F N hN
  refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hE⟩
  · refine ⟨fun s s' h => ?_, fun t => ?_⟩
    · have h1 := hE s
      rw [h] at h1
      exact (b₁ (E s')).unique h1 (hE s')
    · obtain ⟨s, hs, -⟩ := b₁ t
      exact ⟨s, (b₂ s).unique (hE s) hs⟩
  · intro s s' s'' h j
    have hT := hlin F N w₀ (E s) (E s') (SecOps.secAdd (E s) (E s')) s s' 1 (hE s) (hE s') (fun j => by
      simp [SecOps.secAdd, liftFun])
    have e : (1 : F) • s + s' = s'' := fam_ext fun α j => by rw [h]; simp
    rw [e] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ s'').unique (hE s'') hT)
  · intro c s s' hs j
    obtain rfl := (isSmul_iff c s s').1 hs
    obtain ⟨z, hz, -⟩ := b₁ SecOps.secZero
    have hz0 : z = 0 := by
      have h2 := hlin F N w₀ _ _ SecOps.secZero z z 1 hz hz (fun j => by simp [SecOps.secZero])
      have h3 := (b₁ _).unique hz h2
      rw [one_smul] at h3
      exact left_eq_add.1 h3
    have hT := hlin F N w₀ (E s) SecOps.secZero
      (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F c)) (E s)) s z c (hE s) hz (fun j => by
        show _ = _ + 0
        rw [add_zero]
        rfl)
    rw [hz0, add_zero] at hT
    exact congrArg (fun t : GlobalTheory.UT.SecA A F N => t.f j) ((b₂ _).unique (hE _) hT)
  · intro x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := hf.2.1 x hx
      exact ⟨p, (hlabf p).trans hp⟩
    · rintro ⟨p, rfl⟩
      rw [hlabf]
      exact hfN p
  · intro p
    exact (hSF p).1.1
  · intro p
    exact ((hSF p).2 (lab p) (hlab p)).1
  · intro p w θ s s' hw hθ hrel
    obtain ⟨t', ht'⟩ := GlobalTheory.RootShift.exists_isActOf A.isLB θ (E s)
    obtain ⟨s'', hs'', -⟩ := b₁ t'
    have h1 := ((hSF p).2 (lab p) (hlab p)).2 θ hθ w₀ hw₀ w hw (E s) t' s s'' (hE s) hs'' ht'
    obtain rfl := GlobalTheory.ThetaTranslate.phiRel_unique gf p hw.1 hrel h1
    have e := (b₂ s').unique (hE s') hs''
    rw [← e] at ht'
    exact ht'

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantInverseThetaExpansionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_equivariant_inverse_thetaExpansion : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → CharZero R → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G), IsSemiAbelian G → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (w₀ : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))), w₀.IsGen → ∀ lab : QkPt D.toPre F N → (TFK (R := R) F ⟶ A.A), (∀ p, QkToAkU U.toUnifPre F N p (lab p)) → ∃ E, Eqv D.toPre A F N lab E ∧ ∀ s, U.ExpandsF F N w₀ (E s) s := by
  first | exact @GlobalTheory.Mum.exists_eqv_expandsF | exact GlobalTheory.Mum.exists_eqv_expandsF | (intros; apply GlobalTheory.Mum.exists_eqv_expandsF <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreIsoGenericFibreCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_fibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  intro R _ _ _ _ D C W _ _ _ T F _ _ _ hF

  have hρ : Function.Injective ((algebraMap (FractionRing W) F).comp ((algebraMap W (FractionRing W)).comp T.φ)) :=
    (algebraMap (FractionRing W) F).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
  obtain ⟨ga, hga, hy⟩ := Modif.factor_gp R C.toModif F _ (jFK (R := W) F ≫ jK W ≫ T.ξ) hρ (by
    rw [Category.assoc, Category.assoc, T.ξ_π]
    simp only [jK, jFK, spMap, ← Spec.map_comp]
    rfl)
  have hga' : ga = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (hga r).trans (hF r).symm)
  subst hga'
  have hu : jFK (R := W) F ≫ jK W ≫ T.ξ = jFK (R := R) F ≫ C.gp := hy

  have s₁ : IsPullback (pullback.snd (jFK (R := W) F) T.A.A.hom) (pullback.fst (jFK (R := W) F) T.A.A.hom)
      T.A.A.hom (jFK (R := W) F) := (IsPullback.of_hasPullback _ _).flip
  haveI : IsIso T.U.gen.inv.left := ⟨⟨T.U.gen.hom.left, by rw [← Over.comp_left, T.U.gen.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, T.U.gen.hom_inv_id, Over.id_left]⟩⟩
  have s₂ : IsPullback T.U.gen.inv.left T.A.A.hom (pullback.snd T.G.hom (jK W)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w T.U.gen.inv⟩
  have s₃ : IsPullback (pullback.fst T.G.hom (jK W)) (pullback.snd T.G.hom (jK W)) T.G.hom (jK W) :=
    IsPullback.of_hasPullback _ _
  have hW : IsPullback ((pullback.snd (jFK (R := W) F) T.A.A.hom) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β)
      (pullback.fst (jFK (R := W) F) T.A.A.hom) C.G.hom (jFK (R := R) F ≫ C.gp) := by
    have := ((s₁.paste_horiz s₂).paste_horiz s₃).paste_horiz T.cart.1
    rw [← hu]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using this

  have t₁ : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.A.A.hom (jFK (R := R) F) := (IsPullback.of_hasPullback _ _).flip
  have hR : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom ≫ C.α) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.G.hom (jFK (R := R) F ≫ C.gp) := t₁.paste_horiz C.α_cart.1
  refine ⟨(hW.isoIsPullback _ _ hR).hom, inferInstance, hW.isoIsPullback_hom_snd _ _ hR, ?_⟩
  exact hW.isoIsPullback_hom_fst _ _ hR

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreIsoGenericFibreCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_fibre_iso_genericFibre_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  first | exact @GlobalTheory.Mum.Trait.exists_fibre_iso | exact GlobalTheory.Mum.Trait.exists_fibre_iso | (intros; apply GlobalTheory.Mum.Trait.exists_fibre_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_comp_tfk {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    spMap em.toRingHom ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := by
  simp only [TFK, Over.mk_hom, jFK]
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

theorem Trait.exists_lab_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  intro R _ _ _ hR D C j W _ _ _ T F _ _ _ _ em hF f hfi hf1 hf2
  have : CharZero R := hR.2
  have hN : 1 ≤ C.n ^ j := Nat.one_le_pow _ _ C.n_prime.pos
  have hbij := qkPt_algClosure_bijective R D.toPre F em (C.n ^ j) hN
  have hpull : ∀ p' : QkPt T.D'.toPre F (C.n ^ j), ∃ p₁ : QkPt D.toPre F (C.n ^ j),
      p'.y = T.hD.xe.symm p₁.y ∧ IsPullGtF T.φ T.hD F p₁.g p'.g := fun p' =>
    qkPullExists GlobalTheory.globalFns_holds R W T.φ D.toPre T.D'.toPre T.hD F hF (C.n ^ j) p'
  have huniq : ∀ (p' : QkPt T.D'.toPre F (C.n ^ j)) (p₁ p₂ : QkPt D.toPre F (C.n ^ j)),
      p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g →
      p'.y = T.hD.xe.symm p₂.y → IsPullGtF T.φ T.hD F p₂.g p'.g → p₁ = p₂ :=
    fun p' p₁ p₂ h₁ g₁ h₂ g₂ => GlobalTheory.TorusExt.qk_ext (T.hD.xe.symm.injective (h₁.symm.trans h₂))
      (GlobalTheory.ArcPull.pullGt_unique' T.hD g₁ g₂)
  choose P₁ hP₁ using hpull
  choose P hP using fun p' => (hbij.2 (P₁ p')).exists

  let y : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A) := fun p =>
    Over.homMk (spMap em.toRingHom ≫ (C.lab j p).left) (by
      rw [Category.assoc, Over.w, spMap_comp_tfk])
  let g : QkPt D.toPre (Kb R) (C.n ^ j) → (TFK (R := R) F ⟶ TFK (R := R) F ⊗ C.A.A) := fun p => lift (𝟙 _) (y p)
  have hg1 : ∀ p, (g p).left ≫ (fst (TFK (R := R) F) C.A.A).left = 𝟙 _ := fun p => by
    rw [← Over.comp_left, lift_fst]; rfl
  have hg2 : ∀ p, (g p).left ≫ (snd (TFK (R := R) F) C.A.A).left = spMap em.toRingHom ≫ (C.lab j p).left := fun p => by
    rw [← Over.comp_left, lift_snd]; rfl
  have hfst : inv f ≫ (fst (TFK (R := W) F) T.A.A).left = (fst (TFK (R := R) F) C.A.A).left := by
    rw [← hf1, IsIso.inv_hom_id_assoc]
  let lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A) := fun p' =>
    Over.homMk ((g (P p')).left ≫ inv f ≫ (snd (TFK (R := W) F) T.A.A).left) (by
      rw [Category.assoc, Category.assoc, Over.w (snd (TFK (R := W) F) T.A.A), ← Over.w (fst (TFK (R := W) F) T.A.A),
        reassoc_of% hfst, reassoc_of% (hg1 (P p'))])
  have heq : ∀ p', (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β =
      spMap em.toRingHom ≫ (C.lab j (P p')).left ≫ C.α := fun p' => by
    simp only [lab', Over.homMk_left, Category.assoc]
    rw [← hf2, IsIso.inv_hom_id_assoc, reassoc_of% (hg2 (P p'))]
  refine ⟨lab', fun p' => T.lab F em hF j (P p') (P₁ p') p' (lab' p') (hP p') (hP₁ p').1 (hP₁ p').2 (heq p'), ?_⟩
  intro p p₁ p' hE hy hgp
  obtain rfl : p₁ = P₁ p' := huniq p' p₁ (P₁ p') hy hgp (hP₁ p').1 (hP₁ p').2
  obtain rfl : p = P p' := (hbij.2 (P₁ p')).unique hE (hP p')
  exact heq p'

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsGenericFibreTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_torsionLabels_genericFibre_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∃ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ p', QkToAkU T.U.toUnifPre F (C.n ^ j) p' (lab' p')) ∧ ∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α := by
  first | exact @GlobalTheory.Mum.Trait.exists_lab_pull | exact GlobalTheory.Mum.Trait.exists_lab_pull | (intros; apply GlobalTheory.Mum.Trait.exists_lab_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabels

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem traitInv_eqv_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hem
  obtain ⟨f, hfi, hf1, hf2⟩ := GlobalTheory.T.exists_fibre_iso_genericFibre_cover R hR D C W T F hem
  obtain ⟨lab', hq, hm⟩ := GlobalTheory.T.exists_torsionLabels_genericFibre_trait R hR D C j W T F em hem f hfi hf1 hf2
  have hW := T.cdvr
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have : CharZero R := hR.2
  have hcW : CharZero W := charZero_of_injective_ringHom T.inj
  have hsemi : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨w₀, hw₀⟩ := T.U.ext
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hx⟩ := GlobalTheory.T.exists_equivariant_inverse_thetaExpansion W (maximalIdeal W) hW' hcW T.D' T.A T.G T.U hsemi F (C.n ^ j) hodd w₀ hw₀ lab' hq
  obtain ⟨lab, E, Φ, hlab, hE, hΦ, hrel⟩ := GlobalTheory.T.trait_equivariant_bijection_transport_cover R hR D C j wA hwA W T F em hem f hfi hf1 hf2 w₀ hw₀ lab' hm E' hE'
  refine ⟨lab, E, hlab, hE, ?_⟩
  intro F₀ s σ hs hσ Z p p' hβ hG z J J' hJ hJ'
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt T.U.LG.isLB z
  obtain ⟨Jt, hJt⟩ := GlobalTheory.UU.exists_good_pt T.A.isLB z
  have hq1 : (p' ≫ inv f) ≫ f = p' := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hG' : p ≫ T.G.hom = (p' ≫ inv f) ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [hG, ← hf1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hβ' : p ≫ T.β = (p' ≫ inv f) ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    rw [hβ, ← hf2, Category.assoc, IsIso.inv_hom_id_assoc]
  exact (GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion R hR D C j W T F w₀ hw₀ E' hx F₀ (Φ s) σ (hΦ s F₀ hs) hσ Z p (p' ≫ inv f) hβ' hG' z J JG Jt hJ hJG hJt).trans
    (hrel s Z p p' (p' ≫ inv f) hq1 hβ hG' z J J' JG Jt hJ hJ' hJG hJt).symm

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_inverse_expansion_equivariant_labels : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  first | exact @GlobalTheory.Mum.traitInv_eqv_value | exact GlobalTheory.Mum.traitInv_eqv_value | (intros; apply GlobalTheory.Mum.traitInv_eqv_value <;> assumption)
end
end
