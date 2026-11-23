module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGlLatCongOfSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLatSmulBlockLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumFirstBlockBlockDiagonalStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InversePartialFourierSumCompFromBlocks

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section
namespace GlobalTheory.BlockSubstFourier

theorem invFourierSum_comp_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1)
    (Φ : Matrix A (D₁ ⊕ D₂) k → ℂ) (hΦ : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ)
    (M₁ : GL D₁ k) (hM₁ : M₁ ∈ KO k D₁) (M₂ : GL D₂ k) (hM₂ : M₂ ∈ KO k D₂) (X : Matrix A (D₁ ⊕ D₂) k) :
    invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  classical
  have triv : ∀ y ∈ 𝒪[k], ψ y = 1 := fun y hy =>
    (hψ 1).2 le_rfl y (by simpa using (show valuation k y ≤ 1 from hy))
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [compl_block_one] at hΦ ⊢
  set P := Assignment.two.block D₁ D₂ with hP
  have inr_mem : ∀ j : D₂, (Sum.inr j : D₁ ⊕ D₂) ∈ P := fun j => by simp [hP, Assignment.block]
  have inl_nmem : ∀ j : D₁, (Sum.inl j : D₁ ⊕ D₂) ∉ P := fun j => by simp [hP, Assignment.block]
  let eP : D₂ ≃ P := Equiv.ofBijective (fun j => ⟨Sum.inr j, inr_mem j⟩) ⟨fun a b h => by simpa using h, by
    rintro ⟨(j | j), h⟩
    · exact absurd h (inl_nmem j)
    · exact ⟨j, rfl⟩⟩
  have eP_apply : ∀ j, (eP j : D₁ ⊕ D₂) = Sum.inr j := fun j => rfl
  set M := fromBlocks M₁.val 0 0 M₂.val with hM
  set M' := fromBlocks M₁.val 0 0 (invT M₂).val with hM'
  set Nk : Matrix P P k := (invT M₂).val.submatrix eP.symm eP.symm with hNk
  have hNk_apply : ∀ a b, Nk (eP a) (eP b) = (invT M₂).val a b := fun a b => by simp [hNk]
  obtain ⟨u, hu⟩ := invT_mem_KO hM₂
  let N : Matrix P P 𝒪[k] := u.val.submatrix eP.symm eP.symm
  let N' : Matrix P P 𝒪[k] := (u⁻¹).val.submatrix eP.symm eP.symm
  have hNN : N * N' = 1 := by
    simp only [N, N', Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hNmap : N.map (fun x => (x : k)) = Nk := by
    rw [hNk, ← hu]; ext i j; rfl
  have hM₂i := (mem_KO_iff M₂).1 hM₂

  set X₂ : Matrix A D₂ k := X.submatrix id Sum.inr with hX₂
  have hXM₂ : (X * M).submatrix id Sum.inr = X₂ * M₂.val := by
    ext i j; simp [hM, hX₂, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
  have condP : ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ P, Z i j ∈ 𝒪[k]) ↔ ∀ i (j : D₂), Z i (Sum.inr j) ∈ 𝒪[k] := by
    intro Z
    refine forall_congr' fun i => ⟨fun h j => h _ (inr_mem j), fun h j hj => ?_⟩
    rcases j with j | j
    · exact absurd hj (inl_nmem j)
    · exact h j
  have hsum : ∀ (T : Matrix A P k) (Y : Matrix A (D₁ ⊕ D₂) k),
      pairCols P Y T = trace (T.submatrix id eP * (Y.submatrix id Sum.inr)ᵀ) := by
    intro T Y
    simp only [pairCols, trace, Matrix.mul_apply, diag_apply, transpose_apply, submatrix_apply, id]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Equiv.sum_comp eP (fun j => T i j * Y i j)).symm
  have hTN : ∀ T : Matrix A P k, (T * Nk).submatrix id eP = T.submatrix id eP * (invT M₂).val := by
    intro T; ext i j
    simp only [submatrix_apply, id, Matrix.mul_apply]
    rw [← Equiv.sum_comp eP]
    simp [hNk_apply]
  have hset : ∀ T : Matrix A P k, setCols P X T * M' = setCols P (X * M) (T * Nk) := by
    intro T; ext i (j | j)
    · simp [hM, hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
    · have h1 : setCols P (X * M) (T * Nk) i (Sum.inr j) = (T.submatrix id eP * (invT M₂).val) i j := by
        rw [← hTN]; simp only [setCols, Matrix.of_apply, dif_pos (inr_mem j), submatrix_apply, id]; rfl
      rw [h1]
      simp [hM', Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks, setCols, inl_nmem, inr_mem]
      rfl
  have hpair : ∀ T : Matrix A P k, pairCols P (X * M) (T * Nk) = pairCols P X T := by
    intro T
    rw [hsum, hsum, hTN, hXM₂, transpose_mul, invT_val]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ M₂.valᵀ, ← transpose_mul, Units.mul_inv, transpose_one,
      Matrix.one_mul]
  have setCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      setCols P Y (T + T') = setCols P Y T + setCols P 0 T' := by
    intro Y T T'; ext i j
    by_cases h : j ∈ P <;> simp [setCols, h]
  have pairCols_add' : ∀ (Y : Matrix A (D₁ ⊕ D₂) k) (T T' : Matrix A P k),
      pairCols P Y (T + T') = pairCols P Y T + pairCols P Y T' := by
    intro Y T T'; simp [pairCols, add_mul, Finset.sum_add_distrib]
  have hcZ : ∀ z : k, valuation k z ≤ valuation k ((ϖ ^ e : kˣ) : k) → (((ϖ ^ e)⁻¹ : kˣ) : k) * z ∈ 𝒪[k] := by
    intro z hz
    rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
    exact hz
  rw [invFourierSum_apply, invFourierSum_apply]
  by_cases hX : ∀ i, ∀ j ∈ P, X i j ∈ 𝒪[k]
  · have hXM : ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      rw [condP] at hX ⊢
      intro i j
      have := congrFun (congrFun hXM₂ i) j
      simp only [submatrix_apply, id] at this
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (hX i l) (hM₂i.1 l j)
    rw [if_pos hX, if_pos hXM]
    let F : Matrix A P k → ℂ := fun T =>
      Φ (setCols P (X * M) ((ϖ ^ e)⁻¹ • T)) * (ψ (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • T)) : ℂ)
    have step : ∀ S : A → P → Res k e,
        Φ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S) * M') * (ψ (-pairCols P X ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) =
          F (liftRes S * N.map (fun x => (x : k))) := by
      intro S
      rw [hNmap]
      simp only [F]
      rw [← Matrix.smul_mul, ← hset, hpair]
    have hF : ∀ T Z : Matrix A P k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) →
        F (T + Z) = F T := by
      intro T Z hZ
      simp only [F, smul_add, setCols_add', pairCols_add', neg_add, AddChar.map_add_eq_mul]
      have hcZ' : ∀ i j, ((ϖ ^ e)⁻¹ • Z) i j ∈ 𝒪[k] := fun i j => by
        simpa [Units.smul_def] using hcZ _ (hZ i j)
      rw [hΦ.2, triv (-pairCols P (X * M) ((ϖ ^ e)⁻¹ • Z)), mul_one]
      · refine neg_mem (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_)
        exact mul_mem (hcZ' i j) (hXM i j j.2)
      · refine FourierDepth.mem_matLat_smul_blockLat.2 ⟨fun i j hj => ?_, fun i j hj => ?_⟩
        · simpa [setCols, hj] using hcZ' i ⟨j, hj⟩
        · simp [setCols, hj]
    simp only [step]
    exact GlobalTheory.ColSubst.sum_liftRes_mul hϖ e N N' hNN F hF
  · have hXM : ¬ ∀ i, ∀ j ∈ P, (X * M) i j ∈ 𝒪[k] := by
      intro h'
      apply hX
      rw [condP] at h' ⊢
      intro i j
      have hX₂ : X₂ = (X * M).submatrix id Sum.inr * (M₂⁻¹).val := by
        rw [hXM₂, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      have : X i (Sum.inr j) = ((X * M).submatrix id Sum.inr * (M₂⁻¹).val) i j := congrFun (congrFun hX₂ i) j
      rw [this, Matrix.mul_apply]
      exact Subring.sum_mem _ fun l _ => mul_mem (h' i l) (hM₂i.2 l j)
    rw [if_neg hX, if_neg hXM]

end GlobalTheory.BlockSubstFourier
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.InversePartialFourierSumCompFromBlocksStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ (fun Z => Φ (Z * fromBlocks M₁.val 0 0 (invT M₂).val)) X =
        invFourierSum ψ ϖ e (Assignment.one.block D₁ D₂)ᶜ Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  first | exact @GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | exact GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks | (intros; apply GlobalTheory.BlockSubstFourier.invFourierSum_comp_fromBlocks <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveFrameDatumBlockSubstitution

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.FrameSubst

theorem vecMul_bound {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k)
    (hx : ∀ j, valuation k (x j) ≤ valuation k c) (j : n) : valuation k ((x ᵥ* G.val) j) ≤ valuation k c := by
  have hG' := ((mem_KO_iff G).1 hG).1
  simp only [vecMul, dotProduct]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (hx i) ((Valuation.mem_integer_iff _ _).1 (hG' i j))).trans (by rw [mul_one])

theorem vecMul_bound_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {G : GL n k} (hG : G ∈ KO k n) (c : k) (x : n → k) :
    (∀ j, valuation k ((x ᵥ* G.val) j) ≤ valuation k c) ↔ ∀ j, valuation k (x j) ≤ valuation k c := by
  refine ⟨fun h j => ?_, fun h => vecMul_bound hG c x h⟩
  have := vecMul_bound ((KO k n).inv_mem hG) c _ h j
  rwa [vecMul_vecMul, Units.mul_inv, vecMul_one] at this

theorem mem_glLat_fromBlocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {D₁ D₂ : Type} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ϖ : kˣ) (e : ℕ)
    {G₁ : GL D₁ k} {G₂ : GL D₂ k} (h₁ : G₁ ∈ KO k D₁) (h₂ : G₂ ∈ KO k D₂) (G : GL (D₁ ⊕ D₂) k)
    (hG : G.val = fromBlocks G₁.val 0 0 G₂.val) : G ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) := by
  intro x
  have hl : ∀ j, (x ᵥ* G.val) (Sum.inl j) = ((fun i => x (Sum.inl i)) ᵥ* G₁.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  have hr : ∀ j, (x ᵥ* G.val) (Sum.inr j) = ((fun i => x (Sum.inr i)) ᵥ* G₂.val) j := fun j => by
    simp [hG, vecMul, dotProduct, Fintype.sum_sum_type]
  rw [mem_blockLat_two, mem_blockLat_two]
  simp only [hl, hr]
  refine and_congr ?_ (vecMul_bound_iff h₂ _ _)
  have := vecMul_bound_iff h₁ 1 (fun i => x (Sum.inl i))
  simpa using this

theorem isPrimFrame_mul_glLat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [Fintype D] [DecidableEq D] {Λ : Submodule 𝒪[k] (D → k)} (g : GL D k)
    (hg : g ∈ glLat Λ) (X : Matrix A D k) : IsPrimFrame Λ (X * g.val) ↔ IsPrimFrame Λ X := by
  refine ⟨fun h => ?_, fun h => Model.isPrimFrame_mul h g hg⟩
  have := Model.isPrimFrame_mul h g⁻¹ ((glLat Λ).inv_mem hg)
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem fFun_comp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ)
    (H : GL D k) (hH : apow (gdet H) ((Fintype.card D : ℂ) / 2) = 1) (X : Matrix A D k) :
    fFun μ σ ν (fun Y => Ψ (Y * H.val)) X = (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) * fFun μ σ ν Ψ (X * (invT H).val) := by
  classical
  by_cases hX : ∃ h : GL D k, X = X0 k σ * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have e1 : X0 k σ * (invT h).val * (invT H).val = X0 k σ * (invT (h * H)).val := by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc]
    have e2 : smallF μ ν (fun Y => Ψ (Y * H.val)) (Y0 k σ * h.val) = smallF μ ν Ψ (Y0 k σ * (h * H).val) := by
      unfold smallF; congr 1; funext g; simp only [Units.val_mul, Matrix.mul_assoc]
    rw [e1, splitTheta_fFun_frameFirstBlock_mul, splitTheta_fFun_frameFirstBlock_mul, e2, gdet_mul, map_mul, apow_mul, hH, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have hn : (ν (gdet H) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    simp only [Units.val_mul]
    ring
  · have hX' : ¬ ∃ h : GL D k, X * (invT H).val = X0 k σ * (invT h).val := by
      rintro ⟨h, hh⟩
      apply hX
      refine ⟨h * H⁻¹, ?_⟩
      have := congrArg (· * ((invT H)⁻¹).val) hh
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
      rw [this, map_mul, map_inv, Units.val_mul]
    rw [fFun, dite_eq_right hX, fFun, dite_eq_right hX', mul_zero]

theorem phiA_blockSubst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' (D₁ ⊕ D₂) k → ℂ), ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂,
    ∀ X : Matrix A (D₁ ⊕ D₂) k,
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
          (fun Y => Ψ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) Ψ (X * fromBlocks M₁.val 0 0 (invT M₂).val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ν ϖ e Ψ M₁ hM₁ M₂ hM₂ X
  classical
  let H : GL (D₁ ⊕ D₂) k := ⟨fromBlocks (invT M₁).val 0 0 M₂.val, fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val,
    by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩
  have hHinv : (invT H).val = fromBlocks M₁.val 0 0 (invT M₂).val := by
    rw [invT_val]
    show (fromBlocks ((invT M₁)⁻¹).val 0 0 (M₂⁻¹).val)ᵀ = _
    rw [fromBlocks_transpose, invT_inv_val, transpose_transpose, transpose_zero, transpose_zero, ← invT_val]
  have hdet : gdet H = (gdet M₁)⁻¹ * gdet M₂ := by
    rw [← gdet_invT]
    ext
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_fromBlocks_zero₁₂ _ _ _
  have habs : apow (gdet H) ((Fintype.card (D₁ ⊕ D₂) : ℂ) / 2) = 1 := by
    rw [hdet, apow_mul, apow_inv, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₁),
      apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hM₂), one_mul]
  have hfac : (((ν (gdet H))⁻¹ : ℂˣ) : ℂ) = (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) := by
    rw [hdet, map_mul, map_inv, mul_inv, inv_inv, Units.val_mul]
  have hgl : invT H ∈ glLat (blockLat ϖ e (Assignment.two.block D₁ D₂)) :=
    mem_glLat_fromBlocks ϖ e hM₁ (invT_mem_KO hM₂) _ hHinv
  show phiA μ σ ν ϖ e _ (fun Y => Ψ (Y * H.val)) X = _
  rw [← hHinv]
  unfold phiA
  rw [latA_blockLat, compl_block_one, isPrimFrame_mul_glLat (invT H) hgl]
  split_ifs
  · rw [fFun_comp_mul μ σ ν Ψ H habs X, hfac]
  · simp

end GlobalTheory.FrameSubst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimitiveFrameDatumBlockSubstitutionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.primitiveFrameDatum_blockSubstitution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k]
    {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁]
    [Fintype D₂] [DecidableEq D₂] (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Ψ : Matrix A' (D₁ ⊕ D₂) k → ℂ), ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂,
    ∀ X : Matrix A (D₁ ⊕ D₂) k,
      phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
          (fun Y => Ψ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)) Ψ (X * fromBlocks M₁.val 0 0 (invT M₂).val) := by
  first | exact @GlobalTheory.FrameSubst.phiA_blockSubst | exact GlobalTheory.FrameSubst.phiA_blockSubst | (intros; apply GlobalTheory.FrameSubst.phiA_blockSubst <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareFlipEquivariantBlockDiagonalColumnSubstitu

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.SquareFlipCols

theorem squareFlip_blockDiag_cols : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A A' D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D₁ ⊕ D₂) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ),
    IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e → CondLE ϖ e ν → ∀ Φ : Matrix A' (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ →
    ∀ M₁ ∈ KO k D₁, ∀ M₂ ∈ KO k D₂, ∀ X : Matrix A (D₁ ⊕ D₂) k,
      squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) X =
        (ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ) *
          squareFlip μ σ ψ ν ϖ e (Assignment.one.block D₁ D₂) Φ (X * fromBlocks M₁.val 0 0 M₂.val) := by
  intro k _ _ _ _ _ _ A A' D₁ D₂ _ _ _ _ _ _ _ _ μ _ σ ψ ν ϖ e hϖ hψ he hν Φ hΦ M₁ hM₁ M₂ hM₂ X
  have h1 : fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (Z * fromBlocks M₁.val 0 0 M₂.val)) =
      fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val) :=
    funext (GlobalTheory.T.partialFourierSum_firstBlock_blockDiagonal ψ ϖ e hϖ hψ Φ hΦ M₁ hM₁ M₂ hM₂)
  have h2 : phiA μ σ ν ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂))
      (fun Y => fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ (Y * fromBlocks (invT M₁).val 0 0 M₂.val)) =
      ((ν (gdet M₁) : ℂ) * (((ν (gdet M₂))⁻¹ : ℂˣ) : ℂ)) • fun Z => phiA μ σ ν ϖ e
        (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)
          (Z * fromBlocks M₁.val 0 0 (invT M₂).val) :=
    funext fun Z => by rw [Pi.smul_apply, smul_eq_mul]; exact GlobalTheory.T.primitiveFrameDatum_blockSubstitution μ σ ν ϖ e _ M₁ hM₁ M₂ hM₂ Z
  have hd := GlobalTheory.FrameDepth.hasDepth_phiA (hμ := by assumption) k A A' (D₁ ⊕ D₂) μ σ ν ϖ e
    (blockUnits ϖ e (Assignment.one.block D₁ D₂)) _ hϖ he hν
    ((FourierDepth.fourier_exchange k A' (D₁ ⊕ D₂) ψ ϖ e _ hϖ hψ).1 Φ hΦ)
  have h3 : HasDepth ϖ e (blockLat ϖ e (Assignment.one.block D₁ D₂)ᶜ) (phiA μ σ ν ϖ e
      (blockLat ϖ e (Assignment.one.block D₁ D₂)) (fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ)) := by
    rw [← latA_blockLat]; exact hd
  unfold squareFlip
  rw [h1, h2, map_smul, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.T.inversePartialFourierSum_comp_fromBlocks ψ⁻¹ ϖ e hϖ (hasConductor_inv hψ) _ h3 M₁ hM₁ M₂ hM₂ X]

end GlobalTheory.SquareFlipCols
end
end
end
