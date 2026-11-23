module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingComStatement
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfPullSections
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTower

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isSystem_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R))
    (t : ℕ → W.IdealSheafData), IsSystem f I t →
    ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme),
      (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧
      (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧
      ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  intro R _ I W f t ht
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))
      Ideal.Quotient.mk_surjective
  have hmono : ∀ e, Mono (thick R I e) := fun e => by haveI := hci e; infer_instance
  have hfst : ∀ e, (pullback.fst f (thick R I e)).ker = baseIdeal f (I ^ (e + 1)) := by
    intro e
    haveI := hci e
    have h := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W W (pullback f (thick R I e)) f (𝟙 W)
      (pullback.fst f (thick R I e)) (pullback.snd f (thick R I e)) inferInstance inferInstance
      pullback.condition).1
      ⟨pullback.fst f (thick R I e), Category.comp_id _, by
        simpa using IsPullback.of_hasPullback f (thick R I e)⟩
    simpa using h.symm
  have hle : ∀ e, (pullback.fst f (thick R I e)).ker ≤ (t e).subschemeι.ker := fun e => by
    rw [hfst, Scheme.IdealSheafData.ker_subschemeι]
    exact ht.baseIdeal_le e
  let q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) := fun e =>
    haveI := hci e
    IsClosedImmersion.lift (pullback.fst f (thick R I e)) (t e).subschemeι (hle e) ≫ pullback.snd _ _
  have hq : ∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e := fun e => by
    haveI := hci e
    simp only [q, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
  clear_value q
  have hb : ∀ e, ∃ b : (t e).subscheme ⟶ (t (e + 1)).subscheme, b ≫ (t (e + 1)).subschemeι = (t e).subschemeι ∧
      IsPullback b (q e) ((t (e + 1)).subschemeι ≫ f) (thick R I e) := fun e =>
    (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W _ _ f (t (e + 1)).subschemeι (t e).subschemeι (q e)
      inferInstance inferInstance (hq e)).2
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]; exact (ht e).symm)
  choose β hβ using hb
  refine ⟨q, β, hq, fun e => (hβ e).1, fun e => ?_⟩
  have hbot : IsPullback (thickTrans R I e) (𝟙 _) (thick R I (e + 1)) (thick R I e) := by
    haveI := hmono (e + 1)
    refine IsPullback.of_isLimit' ⟨by simp [thickTrans_comp]⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
      (fun s m _ h2 => by simpa using h2)
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, thickTrans_comp]
    exact s.condition.symm
  have hcomm : β e ≫ q (e + 1) = q e ≫ thickTrans R I e := by
    haveI := hmono (e + 1)
    rw [← cancel_mono (thick R I (e + 1))]
    calc (β e ≫ q (e + 1)) ≫ thick R I (e + 1) = β e ≫ (t (e + 1)).subschemeι ≫ f := by
          rw [Category.assoc, hq]
      _ = (t e).subschemeι ≫ f := by rw [← Category.assoc, (hβ e).1]
      _ = q e ≫ thick R I e := hq e
      _ = (q e ≫ thickTrans R I e) ≫ thick R I (e + 1) := by rw [Category.assoc, thickTrans_comp]
  refine IsPullback.of_bot ?_ hcomm hbot
  rw [Category.comp_id, ← hq]
  exact (hβ e).2

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTowerStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (t : ℕ → W.IdealSheafData), IsSystem f I t → ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme), (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧ (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧ ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  first | exact @GlobalTheory.FormalAlg.isSystem_tower | exact GlobalTheory.FormalAlg.isSystem_tower | (intros; apply GlobalTheory.FormalAlg.isSystem_tower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatible

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.Div

theorem resG_eq_inv_mul_appLE {X X' : Scheme.{0}} {H : LB X} {H' : LB X'} {φ : X' ⟶ X}
    (w : LB.Iso H' (H.pull φ)) (k : H.ι) (k' : H'.ι) (a : Γ(X, H.U k)) (b : Γ(X', H'.U k'))
    (h : ∀ z, φ z ∈ H.U k → z ∈ H'.U k' →
      gs φ z _ a = (Geo.Tor.gw w (𝟙 _) z k k').val * gs (𝟙 _) z _ b) :
    resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b =
      ((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val *
        (φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
          (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a := by
  apply fn_ext
  intro x hx
  have hk : φ x ∈ H.U k := (GlobalTheory.Cartier.pull_U H φ _).le hx.1
  have hx' : x ∈ H'.U k' := hx.2
  have e := h x hk hx'
  have h1 : gs (𝟙 X') x _ (resG X' (inf_le_right : (H.pull φ).U (fun _ => k) ⊓ H'.U k' ≤ H'.U k') b) =
      gs (𝟙 X') x _ b := gs_res (𝟙 X') x inf_le_right hx b
  have h2 : gs (𝟙 X') x _ ((φ.appLE (H.U k) ((H.pull φ).U (fun _ => k) ⊓ H'.U k')
      (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le)).hom a) = gs φ x _ a := by
    have := gs_res (𝟙 X') x (inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le) hx ((φ.app (H.U k)).hom a)
    refine Eq.trans ?_ (this.trans ((gs_pull (𝟙 X') φ x (H.U k) hk a).trans (by rw [Category.id_comp])))
    rfl
  have h3 : gs (𝟙 X') x _ (((@id (Γ(X', (H.pull φ).U (fun _ => k) ⊓ H'.U k')ˣ) (w.s (fun _ => k, k')))⁻¹).val) =
      ((Geo.Tor.gw w (𝟙 _) x k k')⁻¹).val := by
    rw [gs_unit (𝟙 X') x _ hx, map_inv]
    rfl
  rw [h1, gs_mul (𝟙 X') x _ hx, h2, h3, e, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem isClosedImmersion_of_veryAmpleBy_compat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  intro R _ X f H n s hH hs X' f' H' s' φ w hH' hs' hf _ hrel
  subst hf
  obtain ⟨hc, hci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff f s).1 hs
  obtain ⟨hc', hci'⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff (φ ≫ f) s').1 hs'
  have heq : GlobalTheory.ProjSpace.toProj (φ ≫ f) s' hc' = φ ≫ GlobalTheory.ProjSpace.toProj f s hc := by
    refine GlobalTheory.ProjSpace.toProj_eq_comp_of_locally hc φ hc' fun z => ?_
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    exact ⟨(H.pull φ).U (fun _ => k) ⊓ H'.U k', ⟨(GlobalTheory.Cartier.pull_U H φ _).ge hk, hk'⟩, k,
      inf_le_left.trans (GlobalTheory.Cartier.pull_U H φ _).le, k', inf_le_right, _,
      fun j => resG_eq_inv_mul_appLE w k k' _ _ fun y hy hy' => hrel j y k k' hy hy'⟩
  have : IsClosedImmersion (φ ≫ GlobalTheory.ProjSpace.toProj f s hc) := heq ▸ hci'
  exact IsClosedImmersion.of_comp_isClosedImmersion φ (GlobalTheory.ProjSpace.toProj f s hc)

end GlobalTheory.Div
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfVeryAmpleSectionsCompatibleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.isClosedImmersion_of_veryAmpleSections_compatible : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R)) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → IsClosedImmersion φ := by
  first | exact @GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat | exact GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat | (intros; apply GlobalTheory.Div.isClosedImmersion_of_veryAmpleBy_compat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjective

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem GlobalTheory.FormalAlg.alg_of_isProjBy : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  intro R _ _ I hc W f hP t ht hp
  obtain ⟨q, β, hq, hβ, hpb⟩ := GlobalTheory.T.compatibleReductionSystem_gives_thickening_tower R I W f t ht
  let Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := fun e => Over.mk (q e)
  let j : ∀ e, (Y e).left ⟶ W := fun e => (t e).subschemeι
  obtain ⟨H, hH, n, s, hs⟩ := hP
  have hL : ∀ e, (H.pull (j e)).IsLB := fun e => LB.isLB_pull hH _
  let t' := fun e => Classical.choose (GlobalTheory.MorAlg.exists_isPull (j e) hH s)
  have ht' : ∀ e, GlobalTheory.MorAlg.IsPull (j e) s (t' e) :=
    fun e => Classical.choose_spec (GlobalTheory.MorAlg.exists_isPull (j e) hH s)
  have hv : ∀ e, GlobalTheory.MorAlg.IsPull (β e) (t' (e + 1)) (t' e) := fun e =>
    GlobalTheory.MorAlg.IsPull.cancel hH (hL _) (hL _) (ht' (e + 1)) (by
      have h1 : β e ≫ j (e + 1) = j e := hβ e
      rw [h1]; exact ht' e)
  choose v hv cv using hv
  have hjR : ∀ e, j e ≫ f = (Y e).hom ≫ thick R I e := hq
  have hva : VeryAmpleBy (Y 0).hom (H.pull (j 0)) (t' 0) := by
    obtain ⟨w, hw, c⟩ := ht' 0
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R W f H n s hH hs _ (Ideal.Quotient.mk (I ^ (0 + 1))) _ _ (j 0) (hjR 0) ?_ _ w _ (hL 0) hw c
    have h₃ : IsClosedImmersion (pullback.lift (j 0) (Y 0).hom (hjR 0) ≫ pullback.fst f (thick R I 0)) := by
      rw [pullback.lift_fst]
      exact inferInstanceAs (IsClosedImmersion (t 0).subschemeι)
    exact IsClosedImmersion.of_comp _ (pullback.fst f (thick R I 0))
  obtain ⟨B, H', s', b, w, hH', hs', hb, -, hw, heq⟩ := GlobalTheory.T.exists_projective_algebraisation_formalEmbedding_complete R I hc Y β hpb (fun e => H.pull (j e)) v
    (fun e => ⟨hL e, hv e⟩) n t' cv hva
  obtain ⟨φ, u, hφ, hu, cu⟩ := GlobalTheory.exists_hom_of_veryAmpleBy R W f H n s hH hs B.left B.hom H' s' hH' hs'.1
    fun d F hF h0 => (mem_vanIdeal _ _ _).1 (heq d F hF fun e => (mem_vanIdeal _ _ _).2 fun k => by
      rw [← hjR]
      exact (ht' e).eqn f hH hF h0 k)
  have hbφ : ∀ e, b e ≫ φ = j e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := GlobalTheory.MorAlg.IsPull.comp hH hH' (hL e) ⟨u, hu, cu⟩ ⟨w e, (hw e).1, (hw e).2⟩
    obtain ⟨w₂, hw₂, c₂⟩ := ht' e
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections R W f H n s hH hs _ _ (t' e) _ _ w₁ w₂ (hL e) ?_ hw₁ hw₂ c₁ c₂
    rw [Category.assoc, hφ, hjR]
    exact (hb e).w
  haveI hci : IsClosedImmersion φ := GlobalTheory.T.isClosedImmersion_of_veryAmpleSections_compatible R W f H n s hH hs B.left B.hom H' s' φ u hH' hs' hφ hu cu
  haveI hBp : IsProper (φ ≫ f) := by
    rw [hφ]; exact GlobalTheory.AbLaw.isProper_of_isProjBy R _ _ ⟨H', hH', n, s', hs'⟩
  refine ⟨φ.ker, ?_, fun e => ?_⟩
  · change IsProper (φ.imageι ≫ f)
    have hg : φ.imageι = inv φ.toImage ≫ φ := (IsIso.eq_inv_comp _).2 φ.toImage_imageι
    rw [hg, Category.assoc]
    infer_instance
  · have key := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W B.left (Y e).left f φ (j e) (q e) hci
      (inferInstanceAs (IsClosedImmersion (t e).subschemeι)) (hq e)).1
      ⟨b e, hbφ e, by rw [hφ]; exact hb e⟩
    rw [key]
    exact Scheme.IdealSheafData.ker_subschemeι (t e)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseOfProjectiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.formalClosedSubschemes_algebraise_of_projective : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsProjBy f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isProjBy | exact GlobalTheory.FormalAlg.alg_of_isProjBy | (intros; apply GlobalTheory.FormalAlg.alg_of_isProjBy <;> assumption)
end
end
