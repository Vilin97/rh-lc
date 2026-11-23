module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlanchLoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasCLMNbar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2Isometry
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Planch
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AdelicConjTransposeBlockMatrixTwoByTwoFin

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LeviH

variable {D : D7}

def bA {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

def bD {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem block_matrix_of_blocks {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    M = blk4 (bA M) (bB M) (bC M) (bD M) := by
  unfold blk4 bA bB bC bD
  rw [Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix]
  simp

theorem upper_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bA (blk4 a b c d) = a := by
  unfold bA blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem upper_right_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bB (blk4 a b c d) = b := by
  unfold bB blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bA_reidx {n : ℕ} (y : M2 n) : bA (reidx y) = y.toBlocks₁₁ := by
  unfold bA reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_reidx {n : ℕ} (y : M2 n) : bB (reidx y) = y.toBlocks₁₂ := by
  unfold bB reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_reidx {n : ℕ} (y : M2 n) : bC (reidx y) = y.toBlocks₂₁ := by
  unfold bC reidx
  rw [Matrix.submatrix_submatrix]
  simp

theorem bB_one {R : Type} [CommRing R] {n : ℕ} : bB (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_right_of_block_matrix]

theorem bA_one {R : Type} [CommRing R] {n : ℕ} : bA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, upper_left_of_block_matrix]

theorem lower_left_of_block_matrix {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) : bC (blk4 a b c d) = c := by
  unfold bC blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bC_one {R : Type} [CommRing R] {n : ℕ} : bC (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 0 := by
  rw [← GlobalTheory.StdUnn.Frame.block_matrix_one, lower_left_of_block_matrix]

theorem bA_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bA M).map f = bA (M.map f) := rfl

theorem bB_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bB M).map f = bB (M.map f) := rfl

theorem bC_map {R S : Type} {n : ℕ} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    (bC M).map f = bC (M.map f) := rfl

theorem compAt_bA (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bA M) = bA (compAt θ τ M) := rfl

theorem compAt_bB (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bB M) = bB (compAt θ τ M) := rfl

theorem compAt_bC (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (M : Mx D (n + n) (n + n)) :
    compAt θ τ (bC M) = bC (compAt θ τ M) := rfl

theorem adj_mul {m n k : ℕ} (x : Mx D m n) (z : Mx D n k) :
    adj (HMul.hMul x z : Mx D m k) = HMul.hMul (adj z) (adj x) := by
  unfold adj
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {n : ℕ} : adj (1 : Mx D n n) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero (cA D)) (map_one (cA D)), Matrix.transpose_one]

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {n : ℕ} (a d : Mx D n n) : adj (blk4 a 0 0 d) = blk4 (adj a) 0 0 (adj d) := by
  unfold adj
  rw [GlobalTheory.StdUnn.Frame.block_matrix_map, GlobalTheory.StdUnn.Frame.blockMatrixTwoByTwoFin_transpose, Matrix.map_zero _ (map_zero (cA D)),
    Matrix.transpose_zero]

theorem unitary_mat {n : ℕ} (g : G D n) :
    adj (mat g) * (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * rat (Jst D n) * mat g = rat (Jst D n) := g.2
  rwa [GlobalTheory.StdUnn.Frame.rat_Jst] at h

end PositivityTheory.Rg.Sw.Glob.LeviH

namespace PositivityTheory.Rg.Sw.Glob

open LeviH in

theorem leviTau : LeviTau := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
  have hθ := hC.hθ
  obtain ⟨hτ, hτ', hfin⟩ := hC.hι.2 y
  have h1 : mat (ι y) * mat (ι y)⁻¹ = 1 := by
    show mat (ι y * (ι y)⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have h2 : mat (ι y)⁻¹ * mat (ι y) = 1 := by
    show mat ((ι y)⁻¹ * ι y) = 1
    rw [inv_mul_cancel]
    rfl
  have hU := unitary_mat (ι y)
  have hlevi := hC.hω.levi (ι y)
  generalize mat (ι y) = M at hτ hτ' hfin h1 h2 hU hlevi
  generalize mat (ι y)⁻¹ = M' at h1 h2
  have hB : bB M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bB_map, hfin, bB_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bB]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bB_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₁₂]
      · rw [hτ' τ' h, bB_one]
  have hC0 : bC M = 0 := by
    apply GlobalTheory.StabAtPlace.mx_ext hθ
    · rw [Matrix.map_zero _ (map_zero (finPart D)), bC_map, hfin, bC_one]
    · intro τ'
      rw [OG.compAt_zero', compAt_bC]
      by_cases h : τ' = τ
      · subst h
        rw [hτ, bC_reidx, hya]
        simp only [mM, Matrix.toBlocks_fromBlocks₂₁]
      · rw [hτ' τ' h, bC_one]
  have hM : M = blk4 (bA M) 0 0 (bD M) := by
    conv_lhs => rw [block_matrix_of_blocks M]
    rw [hB, hC0]
  have hAA' : bA M * bA M' = 1 := by
    have e := congrArg bA h1
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, zero_mul, add_zero] at e
    exact e
  have hA'A : bA M' * bA M = 1 := by
    have e := congrArg bA h2
    rw [hM, block_matrix_of_blocks M', GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, upper_left_of_block_matrix, bA_one, mul_zero, add_zero] at e
    exact e
  have hAD : adj (bA M) * bD M = 1 := by
    rw [hM, adelicConjTranspose_blockMatrixTwoByTwoFin, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Frame.submatrix_fromBlocks_mul] at hU
    have e := congrArg bB hU
    rw [upper_right_of_block_matrix, upper_right_of_block_matrix] at e
    simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one] at e
    exact e
  have hD : bD M = adj (bA M') := by
    have e : adj (bA M') * adj (bA M) = 1 := by rw [← LeviH.adj_mul, hAA', LeviH.adj_one]
    calc bD M = 1 * bD M := (one_mul _).symm
      _ = adj (bA M') * (adj (bA M) * bD M) := by rw [← mul_assoc, e]
      _ = adj (bA M') := by rw [hAD, mul_one]
  have hmat : M = blk4 (bA M) 0 0 (adj (bA M')) := by
    calc M = blk4 (bA M) 0 0 (bD M) := hM
      _ = blk4 (bA M) 0 0 (adj (bA M')) := by rw [hD]
  refine ⟨_, bA M, ?_, ?_, ?_, fun Φ x => hlevi ⟨bA M, bA M', hAA', hA'A⟩ hmat Φ x⟩
  · rw [compAt_bA, hτ, bA_reidx, hya]
    simp only [mM, Matrix.toBlocks_fromBlocks₁₁]
  · intro τ' h
    rw [compAt_bA, hτ' τ' h, bA_one]
  · rw [bA_map, hfin, bA_one]

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayNZ

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem awayNZ : AwayNZ := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  classical
  have hl : ∀ τ', l τ' ≠ 0 := fun τ' => lNe D ψ θ l hC.hψ hC.hθ hC.hl τ'
  let W : AddSubgroup (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ intAE D}
      add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (intAE D).zero_mem
      neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin V.rank) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let Ψ : Mx D V.rank n → ℂ := fun x =>
    evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
      gAway V l s τ (fun τ => compAt θ τ x) * g (fun i j => finPart D (x i j))
  have hΨ : Ψ ∈ awayA θ V n l s τ := Submodule.subset_span ⟨1, g, hg, by simp, rfl⟩
  refine ⟨Ψ, 0, awayIn D n V θ l s τ ε fr hC.hθ hC.hs hC.hfr hl Ψ hΨ, ?_⟩
  have h0 : ∀ τ', compAt θ τ' (0 : Mx D V.rank n) = 0 := fun τ' => by
    ext i j
    simp [compAt]
  have hg0 : g (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = 1 := by
    simp only [g]
    rw [if_pos]
    simp only [Matrix.zero_apply, map_zero]
    exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin V.rank) (Fin n) _)).2 W.zero_mem
  show evalPoly _ _ * gAway V l s τ _ * g _ ≠ 0
  rw [hg0]
  simp only [evalPoly, map_one, one_mul, mul_one, gAway, h0]
  simp

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem opGen_of (hF : FTfact) : OpGen := opGen_of' unipTau leviTau wEx schOps hF

theorem opCLM_of' (hF : FTfact) : OpCLM := opCLM_of unipTau leviTau wEx schOps hF decomp lNe

theorem local_L2_isometry (hF : FTfact) : LocalL2Isometry :=
  local_isometry_of_hypotheses unipTau leviTau wEx schOps hF decomp lNe planchLoc awayNZ

end PositivityTheory.Rg.Sw.Glob
end
end
