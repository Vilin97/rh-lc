module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRelativelyRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoeth
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilledStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (h M : ℕ) (t₁ : S ⟶ Sp (cycAway M)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ lev) (e : ℕ), e.Coprime p → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SiegKerBy (o.toSieg hl) e := by
  first | (exact @GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (exact GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg) | (intros; apply GlobalTheory.UPel.HT.KerBy.siegKerBy_toSieg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigidCyc

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_pullback : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  intro h M hM S S' s s' c o f hamp φ ψ φ₂ ψ₂ g q w l g' q' w' l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have hMu : IsUnit ((M : ℕ) : cycAway M) := isUnit_natCast (show M ≠ 0 by omega)
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (M : K) ≠ 0 := by
      have hu := hMu.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hamp hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hM hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ M = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (GlobalTheory.LowChart.isUnit_zetaAway M hM) c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigidCyc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEqStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.siegelObject_rigidity_identifications_eq : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  first | (exact @GlobalTheory.SiegRigidCyc.eq_of_pullback) | (exact GlobalTheory.SiegRigidCyc.eq_of_pullback) | (intros; apply GlobalTheory.SiegRigidCyc.eq_of_pullback  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseCha

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp

theorem relRep_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  intro p _ D R _ b N h M e hN hNp hM hMo hMp hep Y s c hker hY
  haveI := hY
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback h M (cycAway M) (zetaAway M) Y _ s
    (pullback.fst (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) ≫ s) (pullback.fst _ _) c rfl
  have hker' : SiegKerBy c' e := siegKerBy_pull hc' hker
  obtain ⟨Z, π, u, φu, φ₂u, hpb, hsq, hiso, hfin, hrep⟩ :=
    GlobalTheory.T.harrisTaylor_structures_relatively_representable p D R b N hN hNp h M (cycAway M) (zetaAway M) _ _ (pullback.snd _ _) c' e hep hker'
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A) := fun a => GlobalTheory.SiegelPull.secPull hpb (c'.lev a)
  have hlev : ∀ a, (lev a).left ≫ φu = π ≫ (c'.lev a).left := fun a => GlobalTheory.SiegelPull.secPull_left hpb _
  have hsl : IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev :=
    isSympLev_pull hpb hsq c'.isLB u.isLB hiso hlev (GlobalTheory.UPel.HT.SiegPre.isSympLev c')
  have hlevw : ∀ a, (lev a).left ≫ u.A.hom = 𝟙 Z := fun a => Over.w (lev a)
  refine ⟨Z, π, u, lev, hsl, hfin, ?_, ?_⟩
  · rintro T g t t₁ o l hl ⟨m, hm⟩
    have h1 : SiegPB (o.toSieg hl) (u.toSieg hsl) g := ⟨m.φ, m.φ₂, m.cart, m.sq, m.pol, hm⟩
    have h2 : SiegPB (u.toSieg hsl) c' π := ⟨φu, φ₂u, hpb, hsq, hiso, hlev⟩
    exact pb_comp (pb_comp hc' h2) h1
  · intro T t₀ t t₁ o l hl hS
    have hw : t₀ ≫ s ≫ spMap (Int.castRingHom (cycAway M)) = t ≫ spMap (Int.castRingHom R) :=
      specZIsTerminal.hom_ext _ _
    let g₀ : T ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) :=
      pullback.lift t₀ t hw
    have hg₁ : g₀ ≫ pullback.fst _ _ = t₀ := pullback.lift_fst _ _ _
    have hg₂ : g₀ ≫ pullback.snd _ _ = t := pullback.lift_snd _ _ _
    have hS' : SiegPB (o.toSieg hl) c' g₀ := pb_cancel hc' (by rw [hg₁]; exact hS)
    obtain ⟨φ, φ₂, hφ, hsqφ, hisoφ, hlφ⟩ := hS'
    obtain ⟨z, ⟨hz, m, hm⟩, huniq⟩ := hrep T g₀ t o φ φ₂ hg₂ hφ hsqφ hisoφ
    have hlw : ∀ a, (l a).left ≫ o.A.hom = 𝟙 T := fun a => Over.w (l a)
    refine ⟨z, ⟨by rw [← Category.assoc, hz, hg₁], by rw [← Category.assoc, hz, hg₂], m, fun a => ?_⟩, ?_⟩
    · apply hpb.1.hom_ext
      · rw [Category.assoc, hm, Category.assoc, hlev, ← Category.assoc, hz]
        exact hlφ a
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hlw, Category.assoc, hlevw]
        simp
    · rintro z' ⟨h1', h2', m', hm'⟩
      have hzπ : z' ≫ π = g₀ := pullback.hom_ext (by rw [Category.assoc, h1', hg₁])
        (by rw [Category.assoc, h2', hg₂])
      refine huniq z' ⟨hzπ, m', ?_⟩
      refine GlobalTheory.T.siegelObject_rigidity_identifications_eq h M hM _ T _ t₁ c' (o.toSieg hl) g₀ hker'.1 (m'.φ ≫ φu) φ (m'.φ₂ ≫ φ₂u) φ₂
        (by rw [← hzπ]; exact m'.cart.comp hpb) ⟨?_, ?_⟩ ?_ (fun a => ?_) hφ hsqφ hisoφ hlφ
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.1).trans (Category.assoc _ _ _))))
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.2).trans (Category.assoc _ _ _))))
      · exact (m'.pol.trans o.isLB (pull_isLB u.isLB _) (pull_isLB (pull_isLB c'.isLB _) _)
          (iso_pull m'.φ₂ hiso)).trans o.isLB (pull_isLB (pull_isLB c'.isLB _) _) (pull_isLB c'.isLB _)
          (iso_pull_pull c'.isLB φ₂u m'.φ₂)
      · show (l a).left ≫ m'.φ ≫ φu = g₀ ≫ (c'.lev a).left
        rw [← Category.assoc, hm' a, Category.assoc, hlev, ← Category.assoc, hzπ]

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseChaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  first | (exact @GlobalTheory.UPel.HT.relRep_siegel) | (exact GlobalTheory.UPel.HT.relRep_siegel) | (intros; apply GlobalTheory.UPel.HT.relRep_siegel  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfIsQProjOverNoethStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsQProjOver f → IsLocallyNoetherian X := by
  first | exact @GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | exact GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth | (intros; apply GlobalTheory.isLocallyNoetherian_of_isQProjOver_noeth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullb

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CycAwayQProj

theorem finiteType_closure {K : Type} [CommRing K] {s : Set K} (hs : s.Finite) :
    (Int.castRingHom (Subring.closure s)).FiniteType := by
  have h : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have e : Algebra.adjoin ℤ s ≃+* Subring.closure s :=
    RingEquiv.subringCongr (s := (Algebra.adjoin ℤ s).toSubring) (by rw [Algebra.adjoin_int]; rfl)
  have h' : Algebra.FiniteType ℤ (Subring.closure s) := h.equiv (AlgEquiv.ofRingEquiv (f := e) fun x => by simp)
  have := RingHom.finiteType_algebraMap.2 h'
  rwa [RingHom.eq_intCast' (algebraMap ℤ (Subring.closure s))] at this

theorem finiteType_cycAway (M : ℕ) : (Int.castRingHom (cycAway M)).FiniteType :=
  finiteType_closure (Set.toFinite _)

theorem isQProjOver_comp_spMap {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : f.FiniteType)
    {Y : Scheme.{0}} {s : Y ⟶ Sp B} (h : IsQProjOver s) : IsQProjOver (s ≫ spMap f) := by
  obtain ⟨_, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  have : LocallyOfFiniteType (spMap f) := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 hf
  exact (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB _).2 ⟨inferInstance, hL⟩

theorem isQProjOver_of_isFinite_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) :=
  fun M _ _ _ _ _ _ hs _ π _ =>
    isQProjOver_comp_of_isFinite π
      (isQProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isQProjOver_comp_spMap (finiteType_cycAway M) hs))

end GlobalTheory.CycAwayQProj
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiProjectiveOfFiniteOverCyclotomicAwayPullbStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback : ∀ (M : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R], IsUnit ((M : ℕ) : R) → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)), IsQProjOver s → ∀ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))), IsFinite π → IsQProjOver (π ≫ pullback.snd _ _) := by
  first | (exact @GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (exact GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback) | (intros; apply GlobalTheory.CycAwayQProj.isQProjOver_of_isFinite_pullback  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorAuxiliarySymplecticLevelRepresentabl

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem harrisTaylorModuli_symplecticLevel_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → SDRep (Module.finrank ℤ D.La / 2) M e → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M := by
  intro p _ D R _ _ b N M e hN hNp hM hMo hMp hep _ hdual hSD
  obtain ⟨X, s, u, hku, -, hqs, huniv⟩ := hSD
  have hMR : IsUnit ((M : ℕ) : R) := b.unit M hMp
  have hqP : IsQProjOver (𝟙 _ ≫ pullback.snd (s ≫ spMap (Int.castRingHom (cycAway M)))
      (spMap (Int.castRingHom R))) :=
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs _ (𝟙 _) inferInstance
  rw [Category.id_comp] at hqP
  have hLN := GlobalTheory.T.isLocallyNoetherian_of_isQProjOver_noetherian R _ _ hqP
  obtain ⟨Z, π, v, lev, hlev, hfin, hfwd, hback⟩ :=
    GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange p D R b N (Module.finrank ℤ D.La / 2) M e hN hNp hM hMo hMp hep X s u hku hLN
  refine ⟨Z, π ≫ pullback.snd _ _, π ≫ pullback.fst _ _ ≫ s, v, lev, hlev,
    GlobalTheory.T.isQuasiProjective_of_finite_over_cyclotomicAway_pullback M R hMR X s hqs Z π hfin, ?_⟩
  intro S t t₁ o l hl
  have heS : IsUnit ((e : ℕ) : Γ(S, ⊤)) := by
    have h := (b.unit e hep).map ((t.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    simpa using h
  obtain ⟨f₀, ⟨hf₀s, hf₀pb⟩, hf₀u⟩ :=
    huniv S t₁ (o.toSieg hl) heS (GlobalTheory.T.harrisTaylor_siegelObject_polarisationKernel_killed p D R b N S t o _ M t₁ l hl e hep hdual)
  obtain ⟨g, ⟨hg₁, hg₂, hgm⟩, hgu⟩ := hback S f₀ t t₁ o l hl hf₀pb
  refine ⟨g, ⟨hg₂, ?_, hgm⟩, ?_⟩
  · rw [← hf₀s, ← hg₁]
    simp only [Category.assoc]
  · rintro g' ⟨hg's, hg's₁, hg'm⟩
    have hfst : g' ≫ π ≫ pullback.fst _ _ = f₀ :=
      hf₀u _ ⟨by simpa only [Category.assoc] using hg's₁, hfwd S g' t t₁ o l hl hg'm⟩
    exact hgu g' ⟨hfst, hg's, hg'm⟩

end GlobalTheory.UPel.HT
end
end
end
