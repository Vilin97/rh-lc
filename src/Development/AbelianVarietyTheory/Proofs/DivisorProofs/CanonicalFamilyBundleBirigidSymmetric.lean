module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismsAdjointPair
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibre
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStar

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.OLinRosati

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}


omit [IsDomain R] in
theorem thickMap_pullback_map {G : Over (Sp R)} (b : G ⟶ G) (e : ℕ) :
    thickMap R I e G ≫ ((Over.pullback (thick R I (e + 1))).map b).left =
      ((Over.pullback (thick R I e)).map b).left ≫ thickMap R I e G := by
  apply pullback.hom_ext <;>
    simp [thickMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc]

theorem linEnd_act {D : DegData R I} {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {o : D.toPre.OAct O}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
    {oA : A.OAct O} {oG : RingAct G O} (h : U.OLinear O o oA oG) (a : O) :
    LinEnd U (o.onB.act a) (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (oG.act a) := by
  haveI := oG.hom a
  refine ⟨oG.hom a, fun e => inferInstance, fun e => thickMap_pullback_map _ e, fun e => h.q_lin e a, fun e => ?_⟩
  exact h.i_lin e a

theorem endData_act {D : DegPre R} {O : Type} [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (a : O) :
    EndData D (o.onB.act a) (o.onB.act (star a)) (DistribSMul.toAddMonoidHom D.X a)
      (DistribSMul.toAddMonoidHom D.X (star a)) :=
  ⟨o.onB.hom a, o.onB.hom (star a), o.onB.rosati a, o.c_lin a, o.c_lin (star a), o.tau_bal a⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D O _ _ _ o A G _ _ U oA oG hG hlin a
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have h₁ := linEnd_act hlin a
  have h₂ := linEnd_act hlin (star a)
  rw [star_star] at h₂
  exact linEnd_adjoint_lbIso R hB D A G hG U _ _ _ _ (endData_act o a) _ _ h₁ h₂

end GlobalTheory.Mum.OLinRosati
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationRosatiAdjointStarStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.linearUniformisation_rosatiAdjoint_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D : DegData R (maximalIdeal R)) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (oA : A.OAct O) (oG : RingAct G O), IsSemiAbelian G → U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  first | exact @GlobalTheory.Mum.OLinRosati.main | exact GlobalTheory.Mum.OLinRosati.main | (intros; apply GlobalTheory.Mum.OLinRosati.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumAxes

theorem one_comp_hom' {S : Scheme.{0}} {X M N : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : X ⟶ M) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem gen_pull_lam {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (c : T ⟶ G2 G) (hc : c ≫ fst G G = 1 ∨ c ≫ snd G G = 1) :
    ∃ t : ((abelian₂ G L).pull c.left).Gen, t.IsGen := by
  have hR : GlobalTheory.CoordToExt.Refines ((abelian₂ G L).pull c.left) L
      (fun p : PUnit × ULift.{0} (Finset (Fin 2)) => c.left ≫ (psum G (x2 G) p.2.down).left)
      (fun p => (-1) ^ (2 - p.2.down.card) * 1) :=
    (GlobalTheory.CoordToExt.refines_self (L := L) _ _).linComb _ _
  refine hR.exists_gen hL (φ' := PEmpty.elim) (ε' := PEmpty.elim) ?_ (LB.oneGen L) GlobalTheory.CoordToExt.isGen_one
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), c.left ≫ (psum G (x2 G) I).left = (psum G ![c ≫ fst G G, c ≫ snd G G] I).left :=
    fun I => by
      have := psum_hom (preHom (G := G) c) (x2 G) I
      have e : (fun i => preHom (G := G) c (x2 G i)) = ![c ≫ fst G G, c ≫ snd G G] := by
        funext i; fin_cases i <;> rfl
      rw [e] at this
      exact congrArg (fun z => z.left) this
  simp only [hp]
  rw [Fintype.prod_prod_type]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  simp only [Finset.univ_unique, Finset.prod_singleton, hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, Finset.univ_eq_empty,
    Finset.prod_empty]
  rcases hc with hc | hc <;> simp [hc]

theorem gen_axes : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (L : LB G'.left), L.IsLB → ∀ (u v : G ⟶ G'), IsMonHom u → IsMonHom v → ∀ P : LB (G2 G).left, P.IsLB →
    LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ u) (snd G G ≫ v)).left) →
    (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧
      (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) := by
  intro S G G' _ _ _ _ L hL u v hu hv P hP hiso
  have hΛ : (abelian₂ G' L).IsLB := GlobalTheory.SabBaseChange.cube_isLB (x2 G') hL
  have key : ∀ a : G ⟶ G2 G, (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ fst G' G' = 1 ∨
      (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)) ≫ snd G' G' = 1 → ∃ t : (P.pull a.left).Gen, t.IsGen := by
    intro a ha
    have h1 : LBIso (P.pull a.left) ((abelian₂ G' L).pull (a ≫ lift (fst G G ≫ u) (snd G G ≫ v)).left) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hiso a.left (Over.comp_left ..)
    obtain ⟨t, ht⟩ := gen_pull_lam hL _ ha
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hΛ _) (pull_isLB hP _) h1.symm t ht
  refine ⟨key _ (Or.inl ?_), key _ (Or.inr ?_)⟩
  · rw [Category.assoc, lift_fst, lift_fst_assoc]; exact one_comp_hom' u
  · rw [Category.assoc, lift_snd, lift_snd_assoc]; exact one_comp_hom' v

end GlobalTheory.MumAxes
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackHomPairTrivialAxesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordBundle_pullback_homPair_trivial_axes : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (u v : G ⟶ G'), IsMonHom u → IsMonHom v → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ u) (snd G G ≫ v)).left) → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.MumAxes.gen_axes | exact GlobalTheory.MumAxes.gen_axes | (intros; apply GlobalTheory.MumAxes.gen_axes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MumSymPull

open GlobalTheory.CoordToExt GlobalTheory.RigidTranslate

variable {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}

omit [IsCommMonObj G] in
theorem comp_psum {n : ℕ} (h : T' ⟶ T) (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    h ≫ psum G x I = psum G (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rw [← Category.assoc, comp_toUnit]
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    exact MonObj.comp_mul _ _ _

def chartPullCube (L : LB G.left) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    ChartPull (cubeLB G ![s', t'] L) (cubeLB G ![s, t] L) h.left :=
  chartPullSame L _ _ _ h.left fun I => by
    rw [← Over.comp_left, comp_psum]
    congr 2
    funext k
    fin_cases k
    exacts [hs, ht]

theorem cube_swap (hL : L.IsLB) (s t : T ⟶ G) : LBIso (cubeLB G ![s, t] L) (cubeLB G ![t, s] L) := by
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ isGen_one fun U _ f => ?_
  refine (congrArg₂ (· * ·) (Fintype.prod_empty _) (prod_square ![s, t] fun x => f x.left)).trans
    (Eq.symm ((prod_square ![t, s] fun x => f x.left).trans ?_))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, _root_.mul_comm t s]
  rw [mul_right_comm (f _) (f t.left)⁻¹]

theorem cube_pull (hL : L.IsLB) (s t : T ⟶ G) (h : T' ⟶ T) (s' t' : T' ⟶ G) (hs : s' = h ≫ s) (ht : t' = h ≫ t) :
    LBIso (cubeLB G ![s', t'] L) ((cubeLB G ![s, t] L).pull h.left) := by
  have r : LBIso (cubeLB G ![s, t] L) (cubeLB G ![s, t] L) := exists_iso hL rfl _
  exact LBIso.chartPull (chartPullCube L s t h s' t' hs ht) (GlobalTheory.chartPullPull _ h.left) r

theorem cube_adj {a b : G ⟶ G}
    (H : LBIso (cubeLB G ![fst G G ≫ a, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ b] L)) (s t : T ⟶ G) :
    LBIso (cubeLB G ![s ≫ a, t] L) (cubeLB G ![s, t ≫ b] L) :=
  LBIso.chartPull (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp))
    (chartPullCube L _ _ (lift s t) _ _ (by simp) (by simp)) H

theorem lbIso_swap : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  intro S G G' _ _ _ _ L hL O _ _ oG hadj e f inc _ he hef P hP hPL
  have cI : ∀ s t : G2 G ⟶ G', (cubeLB G' ![s, t] L).IsLB := fun s t => DVR.linComb_isLB _ hL _ _
  have lI : (abelian₂ G' L).IsLB := DVR.linComb_isLB _ hL _ _
  set x : G2 G ⟶ G' := fst G G ≫ inc with hx
  set y : G2 G ⟶ G' := snd G G ≫ inc with hy
  have xe : x ≫ oG.act e = x := by rw [hx, Category.assoc, he]
  have ye : y ≫ oG.act e = y := by rw [hy, Category.assoc, he]
  have h₁ : LBIso P (cubeLB G' ![x, y ≫ oG.act f] L) :=
    hPL.trans hP (pull_isLB lI _) (cI _ _) (cube_pull hL _ _ _ _ _ (by simp) (by simp [hy])).symm
  have h₂ : LBIso (P.pull (lift (snd G G) (fst G G)).left) (cubeLB G' ![y, x ≫ oG.act f] L) :=
    LBIso.chartPull (GlobalTheory.chartPullPull P _)
      (chartPullCube L _ _ (lift (snd G G) (fst G G)) _ _ (by simp [hx, hy]) (by simp [hx, hy])) h₁
  have h₃ := cube_swap hL y (x ≫ oG.act f)
  have h₄ := cube_adj (hadj f) x y
  have h₅ := cube_adj (hadj e) x (y ≫ oG.act (star f))
  have h₆ := cube_adj (hadj e) x (y ≫ oG.act f)
  rw [xe] at h₅ h₆
  have k : (y ≫ oG.act (star f)) ≫ oG.act (star e) = (y ≫ oG.act f) ≫ oG.act (star e) := by
    have := congrArg (fun a => y ≫ oG.act a) hef
    simp only [oG.map_mul] at this
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, ye] at this
    exact this.symm
  rw [k] at h₅
  have h₇ : LBIso (cubeLB G' ![y, x ≫ oG.act f] L) (cubeLB G' ![x, y ≫ oG.act f] L) :=
    h₃.trans (cI _ _) (cI _ _) (cI _ _) (h₄.trans (cI _ _) (cI _ _) (cI _ _)
      (h₅.trans (cI _ _) (cI _ _) (cI _ _) h₆.symm))
  exact h₁.trans hP (cI _ _) (pull_isLB hP _) (h₇.symm.trans (cI _ _) (cI _ _) (pull_isLB hP _) h₂.symm)

end GlobalTheory.MumSymPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundlePullbackInclusionFactorSymmetricStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (L : LB G'.left), L.IsLB → ∀ (O : Type) [Ring O] [StarRing O] (oG : RingAct G' O), (∀ a : O, LBIso (cubeLB G' ![fst G' G' ≫ oG.act a, snd G' G'] L) (cubeLB G' ![fst G' G', snd G' G' ≫ oG.act (star a)] L)) → ∀ (e f : O) (inc : G ⟶ G'), IsMonHom inc → inc ≫ oG.act e = inc → star e * f * e = star e * star f * e → ∀ P : LB (G2 G).left, P.IsLB → LBIso P ((abelian₂ G' L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act f)).left) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) := by
  first | exact @GlobalTheory.MumSymPull.lbIso_swap | exact GlobalTheory.MumSymPull.lbIso_swap | (intros; apply GlobalTheory.MumSymPull.lbIso_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem canon_isBiRig : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  intro R _ _ _ hCN Q G _ _ P hC
  obtain ⟨hP, D', F, A', G', i1, i2, U', oA, oG, inc, pr, hsemi, hlin, hinc, hpr, hip, hpi, hiso⟩ := hC
  have hL : U'.LG.L.IsLB := U'.LG.isLB
  have hros := GlobalTheory.T.linearUniformisation_rosatiAdjoint_star R hCN D' F.O F.o A' G' U' oA oG hsemi hlin
  have hie : inc ≫ oG.act F.e = inc := by rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hf : IsMonHom (inc ≫ oG.act F.f) := by have := oG.hom F.f; infer_instance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.mumfordBundle_pullback_homPair_trivial_axes (Sp R) G G' U'.LG.L hL inc (inc ≫ oG.act F.f) hinc hf P hP hiso
  exact ⟨hP, h1, h2, GlobalTheory.T.mumfordBundle_pullback_inclusion_factor_symmetric (Sp R) G G' U'.LG.L hL F.O oG hros F.e F.f inc hinc hie F.alg.2.1 P hP hiso⟩

end GlobalTheory.Mum
end
end
