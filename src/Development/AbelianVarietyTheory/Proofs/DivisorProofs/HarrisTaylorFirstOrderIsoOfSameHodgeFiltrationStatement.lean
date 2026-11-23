module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Mathlib.RingTheory.Henselian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowersStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBidualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.RingTheory.DualNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedHodgeFiltrationEqOfSameLiftsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Algebra.Azumaya.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueTorsionLiftOfHenselian

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_torsion_lift_of_henselian : ∀ (W : Type) [CommRing W] [HenselianLocalRing W] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (p : Sp W ⟶ S) (N : ℕ), IsUnit (N : W) → ∀ x₀ : Over.mk (spMap (residue W) ≫ p) ⟶ G, x₀ ^ N = 1 → ∃! x : Over.mk p ⟶ G, x ^ N = 1 ∧ spMap (residue W) ≫ x.left = x₀.left := by
  intro W _ _ S G _ _ hG p N hN x₀ hx₀
  have := hG.smooth
  let G' := (Over.pullback p).obj G
  have : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom p))
  have hN' : IsUnit (N : Γ(Sp W, ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom
  have : Etale (mulN G' N).left := GrpTangent.etale_mulN G' hN'
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  let T₀ : Over (Sp W) := Over.mk (spMap (residue W))
  let r : T₀ ⟶ T := Over.homMk (spMap (residue W)) (by simp [T, T₀])
  let e := TorsionLift.ptsEquiv p G T p (Category.id_comp p)
  let e₀ := TorsionLift.ptsEquiv p G T₀ (spMap (residue W) ≫ p) rfl
  have hpow : ∀ {Z : Over (Sp W)} (y : Z ⟶ G'),
      y ^ N = 1 ↔ y.left ≫ (mulN G' N).left = (1 : Z ⟶ G').left := by
    intro Z y
    rw [← GrpTangent.comp_mulN]
    exact ⟨fun h => by rw [← Over.comp_left, h],
      fun h => Over.OverMorphism.ext (by rw [Over.comp_left, h])⟩
  have key : ∀ y₀ : T₀ ⟶ G', y₀ ^ N = 1 → ∃! y : T ⟶ G', y ^ N = 1 ∧ r ≫ y = y₀ := by
    intro y₀ hy₀
    have hone : (1 : T₀ ⟶ G').left = spMap (residue W) ≫ (1 : T ⟶ G').left := by
      rw [← comp_one r, Over.comp_left]
      rfl
    obtain ⟨l, ⟨hl₁, hl₂⟩, hl₃⟩ := existsUnique_lift_of_etale_of_henselian (mulN G' N).left
      (residue W) residue_surjective y₀.left (1 : T ⟶ G').left
      (by rw [(hpow y₀).1 hy₀, hone])
    have hlw : l ≫ G'.hom = T.hom := by
      rw [← Over.w (mulN G' N), ← Category.assoc, hl₂]
      exact Over.w _
    refine ⟨Over.homMk l hlw, ⟨(hpow _).2 hl₂, Over.OverMorphism.ext hl₁⟩, ?_⟩
    rintro y ⟨hy₁, hy₂⟩
    exact Over.OverMorphism.ext (hl₃ y.left ⟨congrArg Over.Hom.left hy₂, (hpow y).1 hy₁⟩)
  have h := key (e₀.symm x₀) (by rw [← map_pow, hx₀, map_one])
  refine (e.toEquiv.existsUnique_congr fun y => ?_).1 h
  change _ ↔ e y ^ N = 1 ∧ _ ≫ (e y).left = _
  rw [← map_pow, map_eq_one_iff e e.injective, MulEquiv.eq_symm_apply]
  refine and_congr_right fun _ => ?_
  have : (e₀ (r ≫ y)).left = spMap (residue W) ≫ (e y).left := by
    rw [TorsionLift.ptsEquiv_left, TorsionLift.ptsEquiv_left, Over.comp_left, Category.assoc]
    rfl
  rw [← this]
  exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationBundlesCorrespondDeforma

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PolIsoLift

theorem pol_iso : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  intro p _ D R _ b N k _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he hφ φ₂ hsq
  haveI := he
  have hκ : IsNilDP (GlobalTheory.DeRham.epsDP k) := isDPNilpotent_squareZero _
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  have hred : m₁.φ₂ ≫ φ₂ = m₂.φ₂ := by
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, ← Category.assoc, m₁.sq.1, Category.assoc, hφ, m₂.sq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, m₁.sq.2, Category.assoc, hφ, m₂.sq.2]
  have hP' : (o₂.P.pull φ₂).IsLB := pull_isLB o₂.isLB φ₂
  have axis : ∀ (u v : o₁.A ⟶ o₁.A) (u' v' : o₂.A ⟶ o₂.A),
      (lift u v).left ≫ φ₂ = e.hom.left ≫ (lift u' v').left → Triv (ev o₂.P u' v') →
        Triv (ev (o₂.P.pull φ₂) u v) := by
    intro u v u' v' hc h
    rw [triv_ev_iff hP', evc, cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hc, GlobalTheory.CechPic.pull_comp]
    rw [triv_ev_iff o₂.isLB, evc] at h
    rw [h, map_zero]
  have t₁ : Triv (ev (o₂.P.pull φ₂) (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)) := by
    refine axis _ _ (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A) ?_ o₂.rig₁
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd]
      simp
  have t₂ : Triv (ev (o₂.P.pull φ₂) (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)) := by
    refine axis _ _ (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A) ?_ o₂.rig₂
    apply GlobalTheory.AbDual.left_ext (P := o₂.A) (Q := o₂.A)
    · rw [Category.assoc, hsq.1, lift_left_fst_assoc, Category.assoc, lift_left_fst]
      simp
    · rw [Category.assoc, hsq.2, lift_left_snd_assoc, Category.assoc, lift_left_snd, ← Over.comp_left,
        ← Over.comp_left, MonObj.one_comp, MonObj.comp_one]
  have e' : LBIso ((o₂.P.pull φ₂).pull m₁.φ₂) o₀.P := by
    refine (cls_eq_iff (pull_isLB hP' _) o₀.isLB).1 ?_
    rw [cls_pull hP', cls_pull o₂.isLB φ₂ hP', ← GlobalTheory.CechPic.pull_comp, hred,
      ← cls_pull o₂.isLB m₂.φ₂ (pull_isLB o₂.isLB _)]
    exact (cls_eq_iff _ _).2 (LBIso.symm m₂.pol)
  have hL : (o₁.P.pull (lift (𝟙 o₁.A) (𝟙 o₁.A)).left).IsLB := pull_isLB o₁.isLB _
  exact GlobalTheory.BirigidLift.lift_unique (κ := epsDP k)
    (grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting) GlobalTheory.T.dualAbelianScheme_exists_biduality hκ hπ rfl
    o₁.ab hg o₁.ab hg m₁.cart m₁.cart m₁.sq.1 m₁.sq.2 hL o₁.ample hL o₁.ample o₀.isLB o₁.isLB o₁.rig₁ o₁.rig₂
    (LBIso.symm m₁.pol) hP' t₁ t₂ e'

end GlobalTheory.UPel.HT.PolIsoLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationBundlesCorrespondDeformaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (e : o₁.A ≅ o₂.A), IsMonHom e.hom → m₁.φ ≫ e.hom.left = m₂.φ → ∀ φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left, IsSquare e.hom.left φ₂ → LBIso o₁.P (o₂.P.pull φ₂) := by
  first | (exact @GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (exact GlobalTheory.UPel.HT.PolIsoLift.pol_iso) | (intros; apply GlobalTheory.UPel.HT.PolIsoLift.pol_iso  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderIsoOfSameHodgeFiltration

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTFirstOrderIso

theorem isGrpPullback_of_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := by change IsIso ((Over.forget S).map e.hom); infer_instance
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x ≫ e.hom := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y ≫ e.hom := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul, ← MonObj.mul_comp]
  simp [j]

theorem gd : GlobalTheory.Published.GrothendieckDeformation :=
  GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.T.abelianScheme_firstDeRham_structure GlobalTheory.T.print_abelianLifting

theorem liftHom_eps (k : Type) [Field k] :
    GlobalTheory.Published.GrothendieckMessing.LiftHom (epsDP k) (TrivSqZeroExt.fstHom k k k).toRingHom :=
  (gd.at_dualNumber k).2.2

theorem henselian_of_artinian (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
    HenselianLocalRing C := by
  obtain ⟨n, hn⟩ : IsNilpotent (IsLocalRing.maximalIdeal C) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this
  have hz : ∀ k, n ≤ k → (IsLocalRing.maximalIdeal C) ^ k = ⊥ := fun k hk => by
    rw [← Nat.add_sub_cancel' hk, pow_add, hn, zero_mul]; rfl
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
    refine { haus' := fun x hx => ?_, prec' := fun f hf => ⟨f n, fun k => ?_⟩ }
    · have := SModEq.zero.1 (hx n)
      rw [hz n le_rfl, Submodule.bot_smul] at this
      simpa using this
    · rcases le_total k n with h | h
      · exact hf h
      · have e := SModEq.sub_mem.1 (hf h)
        rw [hz n le_rfl, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at e
        rw [e]
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

instance isArtinianRing_dualNumber (k : Type) [Field k] : IsArtinianRing (DualNumber k) := by
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  exact IsArtinianRing.of_finite k (DualNumber k)

end GlobalTheory.HTFirstOrderIso

namespace GlobalTheory.HTFirstOrderIso

theorem eta_pow {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GlobalTheory.UPel.HT.Obj b N s) (a : D.La) (n : ℕ) :
    o.eta (n • a) = o.eta a ^ n := by
  have h0 : o.eta 0 = 1 := by
    have := o.eta_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem comp_pow {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (ρ : T' ⟶ T) (x : T ⟶ G) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp [MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem objMap_of_filLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (g : HdR o₀.A → HdR o₀.A), (∀ x ∈ Fil o₀.A, IsFilLift m₁.cart x (g x)) → (∀ x ∈ Fil o₀.A, IsFilLift m₂.cart x (g x)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ (𝟙 _)) := by
  intro p _ D R _ b N hN3 hNp k _ _ t o₀ s₁ s₂ o₁ o₂ m₁ m₂ g hg₁ hg₂
  have hF := GlobalTheory.T.liftedHodgeFiltration_eq_of_same_lifts k o₀.A o₁.A o₂.A m₁.φ m₂.φ m₁.cart m₂.cart o₁.ab o₂.ab g hg₁ hg₂
  obtain ⟨d₁, hd₁⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₁.A o₁.ab
  obtain ⟨d₂, hd₂⟩ := GlobalTheory.AbelianDim.exists_relDim (DualNumber k) o₂.A o₂.ab
  obtain ⟨e, he, em⟩ := ((liftHom_eps k).exists_iso_iff m₁.cart o₁.ab hd₁ m₂.cart o₂.ab hd₂).2 hF
  have hact : ∀ c : D.O, (o₁.act.act c).left ≫ e.hom.left = e.hom.left ≫ (o₂.act.act c).left := by
    intro c
    haveI := o₁.act.hom c
    haveI := o₂.act.hom c
    haveI := o₀.act.hom c
    have := (liftHom_eps k).unique m₁.cart o₁.ab hd₁ m₂.cart o₂.ab hd₂ (o₀.act.act c)
      (f := o₁.act.act c ≫ e.hom) (f' := e.hom ≫ o₂.act.act c)
      (by rw [Over.comp_left, ← Category.assoc, ← m₁.act c, Category.assoc, em])
      (by rw [Over.comp_left, ← Category.assoc, em, m₂.act c])
    rw [← Over.comp_left, this, Over.comp_left]

  have hNu : IsUnit (N : DualNumber k) := by simpa using (b.unit N hNp).map (Spec.preimage s₂).hom
  have heta : ∀ y : D.La, (o₁.eta y).left ≫ e.hom.left = 𝟙 _ ≫ (o₂.eta y).left := by
    intro a
    haveI := henselian_of_artinian (DualNumber k)
    let π : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
    have hπ : Function.Surjective π := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
    have h2 : RingHom.ker π ^ 2 = 0 := GlobalTheory.FODef.sqZero k k
    have hk : RingHom.ker π ≤ IsLocalRing.maximalIdeal (DualNumber k) := by
      intro x hx
      by_contra hc
      have hu : IsUnit x := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hc
      have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
      rw [h2] at this
      exact (hu.mul hu).ne_zero (by simpa using this)
    obtain ⟨ρ, hρ⟩ : ∃ ρ : k →+* IsLocalRing.ResidueField (DualNumber k),
        ρ.comp π = IsLocalRing.residue (DualNumber k) :=
      ⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨IsLocalRing.residue (DualNumber k), fun x hx => by
          rw [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]; exact hk hx⟩,
        RingHom.liftOfRightInverse_comp _ _ _ _⟩
    have hs : IsSemiAbelian o₂.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ o₂.ab
    let y₁ : Over.mk (𝟙 (Sp (DualNumber k))) ⟶ o₂.A := o₁.eta a ≫ e.hom
    let y₂ : Over.mk (𝟙 (Sp (DualNumber k))) ⟶ o₂.A := o₂.eta a
    have t₁ : y₁ ^ N = 1 := by
      simp only [y₁]
      rw [← pow_comp, ← eta_pow, o₁.eta_ker, MonObj.one_comp]
    have t₂ : y₂ ^ N = 1 := by
      simp only [y₂]
      rw [← eta_pow, o₂.eta_ker]
    have r : spMap π ≫ y₁.left = spMap π ≫ y₂.left := by
      simp only [y₁, y₂, Over.comp_left]
      rw [← Category.assoc, ← m₁.eta a, Category.assoc, em, m₂.eta a]
    have r' : spMap (IsLocalRing.residue (DualNumber k)) ≫ y₁.left =
        spMap (IsLocalRing.residue (DualNumber k)) ≫ y₂.left := by
      rw [← hρ, Cris.spMap_comp, Category.assoc, r, ← Category.assoc]
    let x₀ : Over.mk (spMap (IsLocalRing.residue (DualNumber k)) ≫ 𝟙 (Sp (DualNumber k))) ⟶ o₂.A :=
      toUnit _ ≫ y₂
    have hx₀ : x₀ ^ N = 1 := by
      simp only [x₀]
      rw [← comp_pow, t₂, MonObj.comp_one]
    have hl : x₀.left = spMap (IsLocalRing.residue (DualNumber k)) ≫ y₂.left := by
      simp only [x₀, Over.comp_left]
      congr 1
    obtain ⟨x, -, hu⟩ := GlobalTheory.existsUnique_torsion_lift_of_henselian (DualNumber k) (Sp (DualNumber k)) o₂.A hs
      (𝟙 _) N hNu x₀ hx₀
    have := (hu y₁ ⟨t₁, r'.trans hl.symm⟩).trans (hu y₂ ⟨t₂, hl.symm⟩).symm
    rw [Category.id_comp, ← Over.comp_left]
    exact congrArg Over.Hom.left this
  let φ₂ : (G2 o₁.A).left ⟶ (G2 o₂.A).left :=
    (lift (fst o₁.A o₁.A ≫ e.hom) (snd o₁.A o₁.A ≫ e.hom)).left
  have hsq : IsSquare e.hom.left φ₂ := by
    constructor
    · simp only [φ₂]; rw [← Over.comp_left, lift_fst, Over.comp_left]
    · simp only [φ₂]; rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hpol := GlobalTheory.T.harrisTaylor_polarisation_bundles_correspond_deformations p D R b N k t o₀ s₁ s₂ o₁ o₂ m₁ m₂ e he em φ₂ hsq
  exact ⟨{ φ := e.hom.left
           φ₂ := φ₂
           cart := isGrpPullback_of_iso e
           sq := hsq
           act := hact
           pol := hpol
           eta := heta }⟩

end GlobalTheory.HTFirstOrderIso
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderIsoOfSameHodgeFiltrationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_iso_of_same_hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (s₁ s₂ : Sp (DualNumber k) ⟶ Sp R) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o₂ : GlobalTheory.UPel.HT.Obj b N s₂) (m₁ : GlobalTheory.UPel.HT.ObjMap o₀ o₁ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (m₂ : GlobalTheory.UPel.HT.ObjMap o₀ o₂ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (g : HdR o₀.A → HdR o₀.A), (∀ x ∈ Fil o₀.A, IsFilLift m₁.cart x (g x)) → (∀ x ∈ Fil o₀.A, IsFilLift m₂.cart x (g x)) → Nonempty (GlobalTheory.UPel.HT.ObjMap o₁ o₂ (𝟙 _)) := by
  first | exact @GlobalTheory.HTFirstOrderIso.objMap_of_filLift | exact GlobalTheory.HTFirstOrderIso.objMap_of_filLift | (intros; apply GlobalTheory.HTFirstOrderIso.objMap_of_filLift <;> assumption)
end
end
