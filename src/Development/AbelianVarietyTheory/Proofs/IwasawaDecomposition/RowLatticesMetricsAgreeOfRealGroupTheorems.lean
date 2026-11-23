module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndefiniteSideRowLatticeAdopted
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
import Formalism.LocalRingCardinality.Lemmas
public import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtFieldMain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVecOfNe
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevelsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndefiniteSideRowLatticeAdoptedStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.L2.DIV Formalism.L2.Indef
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indefinite_side_row_lattice_adopted : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ)
    (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S : IndefData (A.side P ψ Zs)) (tup : T → D.what₂.Tup)
    (eRR : (Fin S.D → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V)
    (jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)),
    A.fam.Ok s → RowSideDef3 D A X P ψ Zs S tup eRR jA → X.RRDef → (∀ w, D.what₂.muAt w = tup (S.μ (D.plEq w))) →
    (∀ μ (a : 𝓞 D.what₂.LL), ∀ y ∈ (X.Mtilde μ).carrier, D.what₂.embLL (a : D.what₂.LL) • y ∈ (X.Mtilde μ).carrier) →
    X.RR.L = S.RR.map ((eRR : (Fin S.D → D.what₂.LL) →ₗ[D.what₂.LL] X.RR.V).restrictScalars (𝓞 D.what₂.LL)) := by
  first | exact @GlobalTheory.Adopt.indefinite_side_row_lattice_adopted | exact GlobalTheory.Adopt.indefinite_side_row_lattice_adopted | (intros; apply GlobalTheory.Adopt.indefinite_side_row_lattice_adopted <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMSmulMeasureSelf

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetSharp

open Formalism.IndefR.Mult

section Schur

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_ne_zero_of_ne {M : DSModel V S} {u : MMap M} (hu : u ≠ 0) : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := by
  intro τ
  by_contra h
  push_neg at h
  exact hu (MultilinearMap.ext fun v => (u.map_coord_zero τ (h (v τ))).trans rfl)

theorem ipM_smul_measure_self (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {u : MMap M} {a : ℝ} (ha : 0 ≤ a)
    (hu : u ≠ 0) (h : ∃ c, IsMultIP M μ 𝓕 u u c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 u u = (a : ℂ) * ipM M μ 𝓕 u u := by
  choose w hw using sm_ne_zero_of_ne hu
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 : IsMultIP M (ENNReal.ofReal a • μ) 𝓕 u u ((a : ℂ) * ipM M μ 𝓕 u u) := by
    intro v v'
    obtain ⟨h1, h2⟩ := ipM_spec M μ 𝓕 u u h v v'
    refine ⟨?_, ?_⟩
    · unfold IntegrableOn at h1 ⊢
      rw [Measure.restrict_smul]
      exact h1.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  exact hasPeterssonInner_unique M _ 𝓕 u u w hv0 (ipM_spec M _ 𝓕 u u ⟨_, h1⟩) h1

end Schur

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem norm_sq_rows (hP : Pins R F cG) (Z : ReadL R F X0 Y) (y : Fin ((s1Of R F).D) → D.what₂.LL) :
    ‖D.jEE (Z.eRR y)‖ ^ 2 =
      (RealDat.nP F.lv2 true)⁻¹ * ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ ^ 2 := by
  set z : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)
    ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)) with hz
  have hzn : ‖(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)‖ = ‖z‖ := rfl
  rw [hzn]
  obtain ⟨hinj, -, hip⟩ := hP.char.base.models.HE
  set w := D.jEE (Z.eRR y) with hw
  have hT := Y.tied.sharp.ee w w
  have hJ := Z.jEE y
  have hE : ⟪w, w⟫_ℂ = ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0 (R.HE.e z) (R.HE.e z) := by
    rw [hT]
    show ipMT _ _ _ _ _ = _
    rw [ipMT, hJ]
    show ipM (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 true)⁻¹ • R.ν0) R.fd0
      (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) (PiTensorProduct.lift.symm (PiTensorProduct.lift (R.HE.e z))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hip' : ⟪z, z⟫_ℂ = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) := hip z z
  have ha : (0 : ℝ) ≤ (RealDat.nP F.lv2 true)⁻¹ := (inv_pos.2 (RealDat.nP_pos (F := F.lv2) true)).le
  by_cases hz0 : z = 0
  · have hu : R.HE.e z = 0 := by rw [hz0, map_zero]
    have hw0 : w = 0 := by
      apply Y.Ish.jE.injective
      rw [map_zero]
      apply Subtype.ext
      rw [hJ]
      show PiTensorProduct.lift (R.HE.e z) = 0
      rw [hu, map_zero]
    rw [hw0, hz0, norm_zero, norm_zero]
    ring
  · have hu : R.HE.e z ≠ 0 := fun h => hz0 (hinj (h.trans (map_zero _).symm))
    have hex : ∃ c, IsMultIP (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) c := by
      by_contra hno
      have h0 : ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e z) (R.HE.e z) = 0 := by
        unfold ipM
        rw [dite_eq_right hno]
      exact hz0 (inner_self_eq_zero.1 (hip'.trans h0))
    rw [ipM_smul_measure_self (R.MY 0) R.ν0 R.fd0 ha hu hex, ← hip'] at hE
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ _ _ _ _ z, hE]
    exact Complex.re_ofReal_mul _ _

theorem majAt_rows_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR x) (Z.eRR y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hR := (complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim).rowHyp true
  have hn := hR.h4pos.2.2 true
  have hv0 := (pins_card_index_ranks D G Pl0 I0 T A3 Ks R F cG hP).2.2.2.2
  refine fun x y => GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ _ Z.eRR.toLinearMap (fun y => ?_) x y
  have hL : Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) = ‖D.jEE (Z.eRR y)‖ := by
    rw [hv0]; exact D.jEE_norm _
  have hr : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y y =
      (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) *
        ⟪(R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y), (R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y)⟫_ℂ :=
    PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr true hR.h2 hn y y
  show Formalism.HermitianLatticesTheory.normAt (RowSide.sharp D).RR.b (RowSide.sharp D).RR.X A3.A.v0 (Z.eRR y) ^ 2 =
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) (s1Of R F).XE A3.A.v0 y ^ 2
  rw [hL, norm_sq_rows hP Z y]
  refine Eq.trans ?_ (Formalism.BasicNotions.normAt_sq_eq_majAt _ _ _ _).symm
  rw [hr, inner_self_eq_norm_sq_to_K, Complex.re_ofReal_mul]
  norm_cast

end GlobalTheory.Mem.R3.MetSharp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajAtSmulRightOf

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetBase

open Formalism.HermitianLatticesTheory

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fcoord_smul_emb (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i; simp [vecAt, map_mul]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem fcoord_add_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i; simp [vecAt, map_add (f := _)]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem majAt_add_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  simp only [majAt, fcoord_add_of b X v x x', Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem majAt_add_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  simp only [majAt, fcoord_add_of b X v y y', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_smul_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v x (a • y) = v.embedding a * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_self_eq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = (((normAt b X v x) ^ 2 : ℝ) : ℂ) := by
  unfold normAt cnorm majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem majAt_eq_of_diag {V' ι' : Type} [AddCommGroup V'] [Module K V'] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Module.Basis ι' K V')
    (X' : InfinitePlace K → Matrix ι' ι' ℂ) (v : InfinitePlace K) (e : V' →ₗ[K] V)
    (hv : ∃ a : K, star (v.embedding a) ≠ v.embedding a)
    (h : ∀ x, majAt b X v (e x) (e x) = majAt b' X' v x x) (x y : V') :
    majAt b X v (e x) (e y) = majAt b' X' v x y := by
  have hadd : ∀ x y : V', (majAt b X v (e x) (e y) - majAt b' X' v x y) +
      (majAt b X v (e y) (e x) - majAt b' X' v y x) = 0 := by
    intro x y
    have h0 := h (x + y)
    have h1 := h x
    have h2 := h y
    simp only [map_add (f := _), majAt_add_left_of, majAt_add_right_of] at h0
    linear_combination h0 - h1 - h2
  obtain ⟨a, ha⟩ := hv
  have h3 := hadd x (a • y)
  simp only [map_smul, majAt_smul_left_of, majAt_smul_right_of] at h3
  have h4 := hadd x y
  have h5 : (v.embedding a - star (v.embedding a)) * (majAt b X v (e x) (e y) - majAt b' X' v x y) = 0 := by
    linear_combination h3 - star (v.embedding a) * h4
  have h6 : v.embedding a - star (v.embedding a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left h6)

end Polar

theorem exists_nonreal {K : Type} [Field K] (v : InfinitePlace K) (hv : v.IsComplex) :
    ∃ a : K, star (v.embedding a) ≠ v.embedding a := by
  by_contra hc
  push_neg at hc
  apply InfinitePlace.not_isReal_iff_isComplex.2 hv
  rw [InfinitePlace.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact hc a

end GlobalTheory.Mem.R3.MetBase

namespace GlobalTheory.Mem.R3.MetBase



theorem metric_base_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s0Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH x y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr false := (hCx.what₂ false).1
  have hE : R.models_HE := hP.char.base.models.HE
  have hn : 0 < RealDat.nP F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hv0 : A3.A.v0 = InfinitePlace.mk D.what₂.embLL := R.hv0
  have hcx : ∃ a : D.what₂.LL, star (A3.A.v0.embedding a) ≠ A3.A.v0.embedding a := by
    haveI := (GlobalTheory.ptField_main D).1
    exact exists_nonreal _ (IsTotallyComplex.isComplex _)
  refine majAt_eq_of_diag _ _ _ _ _ Z.eRR0.toLinearMap hcx ?_ x y
  intro x
  have hR := PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr false h2 hn x x

  set w := (R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding x) with hw
  set z := X0.s.jEE (Z.eRR0 x) with hz
  set u : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) w with hu
  have hjE := Z.jEE0 x
  rw [← hz] at hjE
  change _ = PiTensorProduct.lift (R.HE.e u) at hjE
  have hee := Y.tied.base.ee z z
  have hnorm := X0.s.jEE_norm (Z.eRR0 x)
  have hL : Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) = ⟪z, z⟫_ℂ := by
    rw [majAt_self_eq, hv0, hnorm, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hK : ⟪z, z⟫_ℂ = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
    by_cases hT : R.HE.e (u) = 0
    · have h0 : u = 0 := hE.1 (hT.trans (map_zero _).symm)
      have hz0 : Y.Iz.jE z = 0 := by
        apply Subtype.ext
        rw [hjE, hT, map_zero]
        rfl
      have hz1 : z = 0 := Y.Iz.jE.map_eq_zero_iff.1 hz0
      rw [hz1, h0]
      simp
    · obtain ⟨v, hv⟩ := GlobalTheory.KapRedII.exists_vec_of_ne hT
      rw [hee]
      show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.ν0) R.fd0 _ _ = _
      rw [hjE, ipMT, LinearEquiv.symm_apply_apply, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ (inv_pos.2 hn) v hv, ← hE.2.2]
  change Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XE F.cr false) A3.fam3.base3.v0 x x
  rw [hL, hK, hR]
  have hc : ∀ (s : Bool) (c : ℂ), starRingEnd ℂ c = c → Formalism.IndefR.Links.cj s c = c := by
    intro s c h
    cases s <;> simp [Formalism.IndefR.Links.cj, h]
  change _ = _ * Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) ⟪u, u⟫_ℂ
  rw [hc _ _ (inner_conj_symm u u)]
  rfl

end GlobalTheory.Mem.R3.MetBase
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLatticesMetricsAgreeOfRealGroupTheorems

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem rowLat_ties : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HLatTie (RowSide.sharp D).RR (A3.indefDown (s1Of R F)).RR (A3.indefDown (s1Of R F)).XE Z.eRR ∧ HLatTie X0.s.RR (A3.indefDown (s0Of R F)).RR (A3.indefDown (s0Of R F)).XE Z.eRR0 := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hD := GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok : A3.A.fam.Ok 1 := hH.ok.ok2
  have hmu1 : ∀ w, D.what₂.muAt w = Y.tup ((A3.indefDown (s1Of R F)).μ (D.plEq w)) := fun w => Y.muAt w
  have hmu0 : ∀ w, D.what₂.muAt w = Y.tup ((A3.indefDown (s0Of R F)).μ (D.plEq w)) := fun w => Y.muAt w
  have h1 := GlobalTheory.T.indefinite_side_row_lattice_adopted D G Pl0 T D.R.m A3.A 1 D.what₂.EE (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))
    (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA hok hD.1 Z.rr hmu1 Y.stable
  have h0 := GlobalTheory.T.indefinite_side_row_lattice_adopted D G Pl0 T D.R.m A3.A 1 D.what₂.EE0 X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))
    (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 hok hD.2 Z.rr0 hmu0 Y.stable0
  have m1 := GlobalTheory.Mem.R3.MetSharp.majAt_rows_fixed D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have m0 := GlobalTheory.Mem.R3.MetBase.metric_base_fixed D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  refine ⟨⟨h1, fun v x y => ?_⟩, ⟨h0, fun v x y => ?_⟩⟩
  · by_cases hv : v = A3.A.v0
    · subst hv; exact m1 x y
    · exact Z.met v hv x y
  · by_cases hv : v = A3.A.v0
    · subst hv; exact m0 x y
    · exact Z.met0 v hv x y

end GlobalTheory.Mem.R3
end
end
