module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
public import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlaceStatement
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlaceStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinear

section

@[expose] public section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x

    rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinearStatement

section

@[expose] public section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  first | exact @GlobalTheory.oLatTie_fg_span_top | exact GlobalTheory.oLatTie_fg_span_top | (intros; apply GlobalTheory.oLatTie_fg_span_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TargetMtOfAmbTie

section

@[expose] public section

open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.AmbTieStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexForm

section

@[expose] public section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]

    simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]

    simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie


open GlobalTheory.AmbNormTie in
theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormAtStandardFrameEqNormComplexFormStatement

section

@[expose] public section

open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  first | exact @GlobalTheory.AmbNormTie.normAt_frm_mk | exact GlobalTheory.AmbNormTie.normAt_frm_mk | (intros; apply GlobalTheory.AmbNormTie.normAt_frm_mk <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmbExOfRx

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
  NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AmbCrd

open Formalism.L2.DIV Formalism.L2.Rows

theorem majAt_frm {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (h : PosAt H v) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (frm H) v x y = hAt H v x y := by
  have hp := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H v h
  rw [majAt_eq, frm_of_posDef H v hp, (frameOfSpec _ _ hp).2]
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

section Level

variable (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rNab_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) :
    rNab D A P ψ t2 = (rNab D A P ψ t1).map ((rdx h).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  subst e
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, rdx_refl]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩

theorem majAt_rdx {t1 t2 : T} (e : t1 = t2) (h : rDim D A P ψ t2 = rDim D A P ψ t1) (v : InfinitePlace D.what₂.LL)
    (hp : PosAt (rH D A P ψ t1) v) (x y : Fin (rDim D A P ψ t1) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (frm (rH D A P ψ t2)) v (rdx h x) (rdx h y) =
      hAt (rH D A P ψ t1) v x y := by
  subst e
  have := D.tcLL
  rw [rdx_refl, rdx_refl]
  exact majAt_frm _ v hp x y

end Level

theorem tie_level (D : D7) {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ} (A : FamIn D.what₂.LL G Pl0 T m)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D (A.comap f μ0') P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D (A.comap f μ0') S Fm P ψ tup), AmbTie D (A.comap f μ0') S Fm P ψ tup j' J := by
  have := D.tcLL
  let Fm : AmbForm D S :=
    { MtH := fun μ => toHLat (frm (rH D A P ψ (tp μ))) (rNab D A P ψ (tp μ))
      jAmb := j
      MtH_good := fun μ _ => ⟨frm_det _, GlobalTheory.T.fg_span_top_of_lattice_compatible_semilinear D.what₂.embLL (S.Mtilde μ) (j μ) _ (hF μ).li (hL μ)⟩
      jAmb_basis := fun μ _ => by
        show LinearIndependent ℂ (fun i => j μ (Pi.basisFun D.what₂.LL _ i)) ∧
          Submodule.span ℂ (Set.range (fun i => j μ (Pi.basisFun D.what₂.LL _ i))) = ⊤
        simp only [Pi.basisFun_apply]
        exact ⟨(hF μ).li, (hF μ).span⟩
      jAmb_lat := fun μ _ x => (hL μ).2 x
      jAmb_gen := fun μ _ => (hL μ).1
      jAmb_norm := fun μ _ x => GlobalTheory.T.normAt_standardFrame_eq_norm_complexForm D.what₂.embLL D.starLL_cx (j μ) _ _ _ (hF μ) x }
  let J : AmbIds D (A.comap f μ0') S Fm P ψ tup := ⟨fun s _ => rdx (hs s).1⟩
  refine ⟨Fm, J, ⟨fun s _ x => ?_, fun s _ => ?_, fun s _ v hv x y => ?_⟩⟩
  · refine (hs s).2 _ x fun a a' e => ?_
    show x (Fin.cast (hs s).1 a) = x a'
    congr 1
    exact Fin.ext e
  · exact rNab_rdx D A P ψ (hf s) _
  · exact majAt_rdx D A P ψ (hf s) _ v hv x y

-- Transport the dependent maps and ties along an explicit family equality.
private theorem tie_level_of_comap_eq (D : D7) {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)
    {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (tp : D.what₂.Tup → T)
    (j : ∀ μ, (Fin (rDim D A P ψ (tp μ)) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb μ)
    (E : ∀ μ, Matrix (Fin (rDim D A P ψ (tp μ))) (Fin (rDim D A P ψ (tp μ))) D.what₂.LL)
    (op : ∀ μ, S.Amb μ →ₗ[ℂ] S.Amb μ)
    (hF : ∀ μ, FormsTie D.what₂.embLL (j μ) (rH D A P ψ (tp μ)) (E μ) (op μ))
    (hL : ∀ μ, OLatTie D.what₂.embLL (S.Mtilde μ) (j μ) (rNab D A P ψ (tp μ)))
    (f : T' → T) (μ0' : T') {A' : FamIn D.what₂.LL G Pl0 T' m}
    (hA : A.comap f μ0' = A') (tup : T' → D.what₂.Tup) (hf : ∀ s, f s = tp (tup s))
    (j' : ∀ s, (Fin (rDim D A' P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] S.Amb (tup s))
    (hs : ∀ s, SameOn (j (tup s)) (j' s)) :
    ∃ (Fm : AmbForm D S) (J : AmbIds D A' S Fm P ψ tup), AmbTie D A' S Fm P ψ tup j' J := by
  subst A'
  exact tie_level D S A P ψ tp j E op hF hL f μ0' tup hf j' hs

private theorem famC_comap_incl {B : Base} {px : PreX B.toPre} (I : ColIn B px)
    (hX : B.fields.Ok) {U V : Set I.ι} (Xg : Finset (R3.Gc B px → B.LL)) (tr : R3.TrI B px)
    (h : R3.tuOf I U ⊆ R3.tuOf I V) :
    (R3.famC I hX V Xg tr).A.comap (TupF.incl h) (mu0F (R3.tuOf I U)) =
      (R3.famC I hX U Xg tr).A := rfl

theorem ambEx_of_rx : ∀ 𝒮 : Slots, 𝒮.Rx = RX → AmbEx 𝒮 := by
  rintro ⟨Rx, Nx, Sx, Ox⟩ h
  dsimp only at h
  subst h
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro Z l
  have x : RXs l.what₂ := l.rx
  have hsub : R3.tuOf w.I (R3.usedOf w.I T l.Wt) ⊆ R3.tuOf w.I Set.univ := fun τ hτ => by
    obtain ⟨a, -, e⟩ := (R3.mem_tuOf w.I).1 hτ
    exact (R3.mem_tuOf w.I).2 ⟨a, Set.mem_univ _, e⟩
  have hf : ∀ s, TupF.incl hsub s = tAll w.I (l.what₂.r.Y.tup s) := fun s => by
    apply Subtype.ext
    show s.1 = w.I.tup (l.what₂.r.Y.tup s)
    have e : l.what₂.r.Y.tup s = R3.ixOf w.I _ s := l.what₂.r.tup_ix s
    rw [e, R3.tup_ixOf]
  have hFam := famC_comap_incl w.I l.what₂.hX l.what₂.r.z.Xg l.what₂.r.z.tr hsub
  obtain ⟨a, J, hJ⟩ := tie_level_of_comap_eq (w.st Z).toD7 (RowSide.sharp _) (famAll l.what₂)
    (R3.lev1 w.I) (R3.chr1 w.I) (tAll w.I) x.all.jA _ _ x.all.formsA x.all.latA
    (TupF.incl hsub) (mu0F _) hFam l.what₂.r.Y.tup hf l.what₂.r.Y.jA x.jA_use
  obtain ⟨a0, J0, hJ0⟩ := tie_level_of_comap_eq (w.st Z).toD7 l.p0.s (famAll l.what₂)
    (R3.lev0 w.I) (R3.chr0 w.I) (tAll w.I) x.all.jA0 _ _ x.all.formsAtBottomLevel x.all.latA0
    (TupF.incl hsub) (mu0F _) hFam l.what₂.r.Y.tup hf l.what₂.r.Y.jA0
    x.movedReadingSameMaps_baseReading_agrees
  exact ⟨a, a0, ⟨J, hJ⟩, ⟨J0, hJ0⟩⟩

end GlobalTheory.AmbCrd

end
end
end
