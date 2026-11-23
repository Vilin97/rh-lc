module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlDetEqOneOfMemUnip
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.RingTheory.Coalgebra.IsFrobenius

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodFormsCoordinateMapMemOfLiftsMem

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open Formalism.IndefR.Mult Formalism.IndefR.Cx
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

theorem mem_of_mem_span_image {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup H]
    [Module ℂ H] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (hj : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => j (b k))
    (N : Submodule K V) {z : V} (hz : j z ∈ Submodule.span ℂ (j '' (N : Set V))) : z ∈ N := by
  by_contra hn
  let b : Fin (Module.finrank K N) → V := fun k => (Module.finBasis K N k : V)
  have hb : LinearIndependent K b := (Module.finBasis K N).linearIndependent.map' N.subtype N.ker_subtype
  have hs : Submodule.span K (Set.range b) ≤ N := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact (Module.finBasis K N k).2)
  have h1 := hj _ (Fin.cons z b) (linearIndependent_finCons.2 ⟨hb, fun h => hn (hs h)⟩)
  have h2 : (fun k => j ((Fin.cons z b : Fin (Module.finrank K N + 1) → V) k)) =
      (Fin.cons (j z) (fun k => j (b k)) : Fin (Module.finrank K N + 1) → H) := by
    funext k
    refine Fin.cases rfl (fun _ => rfl) k
  rw [h2, linearIndependent_finCons] at h1
  refine h1.2 (Submodule.span_le.2 ?_ hz)
  rintro _ ⟨x, hx, rfl⟩
  have h3 := congrArg (fun z : N => (z : V)) ((Module.finBasis K N).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h3

  rw [← h3, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem exists_lvlE_eq {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (y : Fin (S.BaseDimension r X P ψ) → K) : ∃ x, (S.lvlE r P ψ).mulVecLin x = (S.V0E r X P ψ).mulVecLin y := by
  obtain ⟨u, hu⟩ := (image_idempotent_spec K _ (S.gaMat r (goodAt X P ψ))).2.le ⟨y, rfl⟩
  have h : S.gaMat r (goodAt X P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r (idemOf X) := by
    rw [← (group_action_matrix_hom K S G r).2, (idempotent_central K G X hX).2]
    rfl
  refine (image_idempotent_spec K _ (S.gaMat r (lvlIdem P ψ))).2.ge ⟨(S.gaMat r (idemOf X)).mulVec u, ?_⟩
  refine Eq.trans ?_ hu
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]

theorem goodFormsCoordinateMap_apply {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) (b : Bool) (j : Bs.J) (c : Fin (X.dW b j) → ℂ) :
    X.w0C b j c = ∑ k, c k • X.eW b j (X.bW b j Bs.v0 k) := by
  show X.eW b j (∑ k, c k • X.bW b j Bs.v0 k) = _

  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

theorem goodFormsCoordinateMap_mem_of_lifts_mem {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : Formalism.L2.Indef.DefBase K} {Am : Formalism.L2.Indef.DefAmb Bs}
    (X : CxData Am) {fc : Formalism.L2.Indef.DefSub Am → Formalism.L2.Indef.DefFace Bs} (cr : Crd Am fc) (b : Bool) (h5 : X.H5 cr b)
    (j : Bs.J) (t : Bs.Tup) (N : Submodule ℂ (X.W j)) (h : ∀ y, X.θ' j t (X.jL j t (cr.toL X.zs b j t y)) ∈ N)
    (c : Fin (X.dW b j) → ℂ) : X.w0C b j c ∈ N := by
  obtain ⟨d, hd⟩ := (h5 j t).2.ge ⟨c, rfl⟩
  rw [← hd]
  show ∑ k, d k • X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1))) ∈ N
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h _)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem e_j_eOp (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y)) =
      postOn _ (R.eWf i σ) ((R.HW i σ).e ((R.FW i).j σ y)) := by
  have htw : ∀ g, (R.HW i σ).e ((R.FW i).j σ (GlobalTheory.LevelForms.twRep (R.FW i) g y)) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ y)) := by
    intro g
    rw [GlobalTheory.LevelForms.twRep_apply, map_smulₛₗ, map_smul, (hU i σ).2.2, smul_smul, ← map_mul, Units.inv_mul, map_one,
      one_smul]

  rw [GlobalTheory.LevelForms.eOp_eq_sum, map_sum, map_sum]
  simp only [map_smulₛₗ, map_smul, htw]
  refine MultilinearMap.ext fun v => ?_
  simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, postOn_apply, RingHom.id_apply]
  all_goals rfl

theorem exists_w0C_eq (i : Fin D.R.m) {w : (R.HW i (sg0 D A)).H} (h1 : w ∈ R.WS F false i (sg0 D A)) :
    ∃ c, Tw.out (s := twAt D.what₂.embLL A.v0) ((R.toCx F).w0C false i c) = w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 h1
  have hs : ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (RealDat.nP_pos (F := F) false)).ne'
  let c' : Fin ((R.toCx F).dW false i) → ℂ :=
    fun k => cj (twAt D.what₂.embLL A.v0) (c k * ((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ)⁻¹)
  have e1 := goodFormsCoordinateMap_apply (R.toCx F) false i c'
  refine ⟨c', (congrArg (Tw.out (s := twAt D.what₂.embLL A.v0)) e1).trans (Eq.trans ?_ hc)⟩
  show ∑ k, cj (twAt D.what₂.embLL A.v0) (c' k) • (((Real.sqrt (RealDat.nP F false) : ℝ) : ℂ) •
    R.bC F false i (sg0 D A) k) = _
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cj_cj, smul_smul, inv_mul_cancel_right₀ hs]

theorem exists_srcForm_eq (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) (t : T0)
    (Z : Submodule D.what₂.LL (A.fam.L i t).S.Forms) (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) Z) → D.what₂.LL) :
    ∃ x, srcForm A i t F.P0 F.ψ0⁻¹ x = (A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) Z y := by
  obtain ⟨x, hx⟩ := exists_lvlE_eq (A.MtCSD i t) (A.leftGroupActionLift i t) A.X hX F.P0 F.ψ0⁻¹
    (((A.fam.L i t).zE (A.fam.lvlA F.P0 F.ψ0) Z).mulVecLin y)
  exact ⟨x, congrArg (fun u => (A.MtCSD i t).basis.equivFun.symm u) hx⟩

theorem out_lift_toL (i : Fin D.R.m) (t : T0)
    (y : Fin ((A.fam.L i t).dZ (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t)) → D.what₂.LL) :
    (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) =
      Tw.mk (twAt D.what₂.embLL A.v0) (R.thG i t (jVx R i t
        ((A.fam.L i t).toF (A.fam.lvlA F.P0 F.ψ0) ((R.toCx F).zs.Zl i t) y))) := rfl

theorem j_eOp_of_adForm (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif) (i : Fin D.R.m) (t : T0) (ph : ℂ)
    (y : Fin (R.nW i) → D.what₂.LL) (u : (R.HV i t).H) (h0 : adForm R i y = ph • R.thF i t u) :
    (R.FW i).j (sg0 D A) ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) y) = ph • R.thG i t u := by
  have h1 := e_j_eOp R hU i (sg0 D A) y
  unfold adForm at h0
  rw [h0, LinearMap.map_smul, ← hG i t u, ← LinearMap.map_smul] at h1
  exact (hW i _).1 h1

end GlobalTheory.TraceIncl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodLiftOntoOfBase

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TraceIncl

namespace GlobalTheory.BaseTwistIncl

section Rank

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem ws_le_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0)
    (N : Submodule ℂ (R.HW i (sg0 D A)).H) (hN : ∀ x, R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) ∈ N) :
    R.WS F false i (sg0 D A) ≤ N := by
  intro w h1
  obtain ⟨c, hc⟩ := exists_w0C_eq R F i h1
  have h0 : ∀ y, (R.toCx F).θ' i t ((R.toCx F).jL i t (F.cr.toL (R.toCx F).zs false i t y)) ∈
      Tw.sub (twAt D.what₂.embLL A.v0) N := by
    intro y
    obtain ⟨x, hx⟩ := exists_srcForm_eq F hX i t ((R.toCx F).zs.Zl i t) y
    have k5 : ∀ u u' : A.fam.amb.FL i t, u = u' → R.thG i t (jVx R i t u) ∈ N → R.thG i t (jVx R i t u') ∈ N :=
      fun u u' h hu => h ▸ hu
    have k4 := k5 _ _ hx (hN x)
    have k3 := out_lift_toL R F i t y
    exact (congrArg (fun u : (R.HW i (sg0 D A)).H => u ∈ N) k3).mpr k4
  have h2 := goodFormsCoordinateMap_mem_of_lifts_mem (R.toCx F) F.cr false h5 i t _ h0 c
  exact (congrArg (· ∈ N) hc).mp h2

theorem goodLiftOnto_of_base (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hW : R.models_HW) (hG : R.thP_thG) (hU : R.LUnif)
    (h5 : (R.toCx F).H5 F.cr false) (i : Fin D.R.m) (t : T0) (ph : ℂ) (hph : ph ≠ 0) :
    GoodLiftOnto R i t F.P0 F.ψ0⁻¹ ph := by
  intro θ hθ z hz
  refine mem_of_mem_span_image ((R.FW i).j (sg0 D A)) (hU i _).1 _ ?_
  have h1 : (R.FW i).j (sg0 D A) z ∈
      Submodule.span ℂ (Set.range fun x => R.thG i t (jVx R i t (OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x))) := by
    refine ws_le_base R F hX h5 i t _ (fun x => Submodule.subset_span (Set.mem_range_self x)) ?_
    rw [GlobalTheory.LevelForms.ws_eq_span]
    exact Submodule.subset_span ⟨z, hz, rfl⟩
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨x, rfl⟩
  refine (Submodule.smul_mem_iff _ hph).1 ?_
  exact Submodule.subset_span ⟨_, ⟨x, rfl⟩, j_eOp_of_adForm R hW hG hU i t ph _ _ (hθ x)⟩

end Rank

attribute [local instance] GlobalTheory.BigOn.runAlg'

theorem leafTW2_of_isRec : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ s : ℕ, A.fam.Ok s → R.Char F → R.LUnif → BaseLinks R F → TwistedRational R F (fun _ => 1) → LeafTW2 O := by
  intro D G _ _ Pl0 T0 A J inst R F κ v₀ fw L Pm Tp hK EX r c O hrec s hOk hC hU hB hrat
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.tied
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  have main : ∀ v, (∀ j, ClassSumRational R j (R.mu v) F.P0 F.ψ0⁻¹ 1) →
      ∀ j, IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j) := by
    intro v h3 j
    have := lattices_of_tie (T := (r.used v).full) (inst := inst) (R := R)
      (ht v j).1 (ht v j).2 hinc (chi_eq_one_of_mem_base R F hC.grp j)
      ⟨hC.lev, hC.grp.red_L, hC.fam.tie, hC.models, hC.thP, hU, ⟨_, (fw.hv₀ j _).1⟩, (hOk.lifts _ _).act,
        GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP j (R.mu v)⟩
      (hOk.lifts _ _).good hOk.irr (h3 j)
      (goodLiftOnto_of_base R F hOk.irr hC.models.HW hC.thP.thG hU hB.1 _ _ _ one_ne_zero)
    exact ⟨this.1, this.2.1, Formalism.L2.DIV.localization_mono _ this.2.2⟩
  intro w hw
  exact ⟨main w (hrat w hw), main _ (by rw [hC.tup.mu_conj w]; exact hrat w hw)⟩

end GlobalTheory.BaseTwistIncl
end
end
end
