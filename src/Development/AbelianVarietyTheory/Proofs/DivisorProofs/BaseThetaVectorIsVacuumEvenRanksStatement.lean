module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeEqComapStandardLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaProductPowAlgebraicModulusOneAllStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerComapLinearIsometryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerProdOrthogonalBlocksStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalBasisBlockVacuumLatticeBasisFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackBasisThetaEqF0FormStatement
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLatticeEqComapBlockwiseLattice

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem baseLattice_eq_comap_blockwise_lattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) =
      (blkLat (ι := Fin n' × Fin n) (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 B.lamM))).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  have h0 : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) = powLat B.lamM (n * 2) (n' * 2) :=
    Lat0 D cc δ
  rw [h0]

  have himg : ∀ x : Fin 4 × D.what₂.Tau → ℂ,
      B.gC x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) ↔
        x ∈ pow4 B.lamM := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := B.gC.injective hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext z
  simp only [AddSubgroup.mem_comap]
  show (∀ i j, (fun τ => z τ i j) ∈ B.lamM) ↔ ∀ k, (fun w => phi B n n' z (k, w)) ∈ _
  have e : ∀ k, (fun w => phi B n n' z (k, w)) = B.gC (blk D k z) := fun k => rfl
  simp only [e, himg]
  constructor
  · intro h k a
    exact h (posE n n' (k, a)).1 (posE n n' (k, a)).2
  · intro h i j
    have := h ((posE n n').symm (i, j)).1 ((posE n n').symm (i, j)).2
    have e2 : slice ((posE n n').symm (i, j)).2 (blk D ((posE n n').symm (i, j)).1 z) = fun τ => z τ i j := by
      funext τ
      show z τ (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).1
        (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).2 = z τ i j
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    rw [← e2]; exact this

end GlobalTheory.BaseVacuum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLatticeEqComapBlockwiseLatticeStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.la_tor0_stdL_eq_blkLat : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ), TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) = (blkLat (ι := Fin n' × Fin n) (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  first | exact @GlobalTheory.BaseVacuum.baseLattice_eq_comap_blockwise_lattice | exact GlobalTheory.BaseVacuum.baseLattice_eq_comap_blockwise_lattice | (intros; apply GlobalTheory.BaseVacuum.baseLattice_eq_comap_blockwise_lattice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumCoordinateEquivIsometry

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

open scoped BigOperators ComplexConjugate

namespace GlobalTheory.BaseVacuum

theorem gC_sum_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, B.gC x w * conj (B.gC y w) = ∑ w, x w * conj (y w) := by
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have h := B.isomOK x y
  rw [blockFourfold_hOne_eq_hOne] at h
  have e : Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau) = matH (hOne B.L (Fin 4 × D.what₂.Tau)) := rfl
  rw [e] at h
  have h' := h
  simp only [LinearEquiv.coe_coe] at h'
  rw [matH_hOne, matH_hOne] at h'
  exact (div_left_inj' hA).1 h'

theorem phi_isom : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)),
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  intro D cc δ B n n' z z'
  have eR : Formalism.L2.Th1.H.stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z')
      = (∑ p, phi B n n' z p * conj (phi B n n' z' p)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := by
    show matH (hOne B.L (Ix D n n')) _ _ = _
    exact matH_hOne _ _ _
  rw [eR]
  have eL : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z'
      = (∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j)) / ((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℝ) : ℂ) := rfl
  rw [eL, show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  congr 1
  symm
  calc (∑ p, phi B n n' z p * conj (phi B n n' z' p))
      = ∑ k : Fin n' × Fin n, ∑ w, B.gC (blk D k z) w * conj (B.gC (blk D k z') w) := by
        rw [Fintype.sum_prod_type]; rfl
    _ = ∑ k : Fin n' × Fin n, ∑ w, blk D k z w * conj (blk D k z' w) :=
        Finset.sum_congr rfl (fun k _ => gC_sum_conj B (blk D k z) (blk D k z'))
    _ = ∑ p : Ix D n n', blk D p.1 z p.2 * conj (blk D p.1 z' p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j) := ?_
  let e : Ix D n n' ≃ D.what₂.Tau × (Fin (n' * 2) × Fin (n * 2)) :=
    ((Equiv.prodAssoc _ _ _).symm.trans ((posE n n').prodCongr (Equiv.refl _))).trans (Equiv.prodComm _ _)
  rw [Fintype.sum_equiv e (fun p => blk D p.1 z p.2 * conj (blk D p.1 z' p.2))
    (fun q => z q.1 q.2.1 q.2.2 * conj (z' q.1 q.2.1 q.2.2)) (fun p => rfl)]
  simp only [Fintype.sum_prod_type]

end GlobalTheory.BaseVacuum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumCoordinateEquivIsometryStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.blockVacuumCoordinateEquiv_isometry : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)), TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  first | exact @GlobalTheory.BaseVacuum.phi_isom | exact GlobalTheory.BaseVacuum.phi_isom | (intros; apply GlobalTheory.BaseVacuum.phi_isom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVacuumEqKappaPowMulBlockKernels

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem thZero_eq_kappa_pow_mul_prod_kerB : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK →
    ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)),
      B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  intro D cc δ B hS n n' z
  have h4 : tens4 B.thMM = B.kappa • Formalism.L2.KerInert.kerB B := (B.thMM_spec hS).2
  have hk : ∀ k : Fin n' × Fin n,
      B.kappa * Formalism.L2.KerInert.kerB B (blk D k z) =
        ∏ a : Fin 4, B.thMM (fun τ => z τ (posE n n' (k, a)).1 (posE n n' (k, a)).2) := by
    intro k
    have := congrFun h4 (blk D k z)
    rw [Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    rfl
  have hcard : B.kappa ^ (n' * n) = ∏ _k : Fin n' × Fin n, B.kappa := by
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [hcard, ← Finset.prod_mul_distrib]
  simp_rw [hk]
  rw [← Fintype.prod_prod_type' (f := fun k a => B.thMM (fun τ => z τ (posE n n' (k, a)).1 (posE n n' (k, a)).2))]
  rw [Fintype.prod_equiv (posE n n')
    (fun p => B.thMM (fun τ => z τ (posE n n' p).1 (posE n n' p).2))
    (fun q => B.thMM (fun τ => z τ q.1 q.2)) (fun _ => rfl)]
  show tensPow B.thMM (n * 2) (n' * 2) z = _
  unfold tensPow
  rw [← Fintype.prod_prod_type' (f := fun i j => B.thMM (fun τ => z τ i j))]

end GlobalTheory.BaseVacuum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVacuumEqKappaPowMulBlockKernelsStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK → ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  first | exact @GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | exact GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | (intros; apply GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaVectorIsVacuumEvenRanks

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

theorem inter_congr_al {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α α' : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V)
    (F : V → ℂ) (h : ∀ x ∈ Λ₂, α x = α' x) : inter H α Λ₁ Λ₂ F = inter H α' Λ₁ Λ₂ F := by
  funext z
  unfold inter
  congr 1
  exact finsum_congr fun c => by rw [h _ (Quotient.out c : Λ₂).2]

theorem thetaVectorUpToUnits_thZero_of_even : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' →
    StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := by
  intro D cc δ B _ _ hcc hδ _ N N' hN hN'
  obtain ⟨n, hn⟩ := hN
  obtain ⟨n', hn'⟩ := hN'
  obtain rfl : N = n * 2 := by omega
  obtain rfl : N' = n' * 2 := by omega
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  refine ⟨bas B n n', B.kappa ^ (n' * n), GlobalTheory.T.orthonormalBasis_blockVacuumLatticeBasisFamily D cc δ B n n', GlobalTheory.T.kappaProduct_pow_algebraicModulusOneAll D cc δ B _, ?_⟩
  funext z
  obtain ⟨hsc', hF0', hidx', hprod⟩ := GlobalTheory.T.latticeIntertwiner_prod_orthogonal_blocks B.L B.ω₀ B.cq (Fin n' × Fin n) (Fin 4 × D.what₂.Tau)
    (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) hS.betaSemi
    (product_theta_mem B.L B.ω₀ _ hS.per hS.half _ hS.betaStd).1.2 hS.idx₁
  have hH : IsHerm (stdH B.L (Ix D n n')) := (standardFormBasic B.L _).2.1
  have hnat := GlobalTheory.T.latticeIntertwiner_comap_linear_isometry _ _ (formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau (n * 2) (n' * 2))
    (stdH B.L (Ix D n n')) (phi B n n') (fun x y => GlobalTheory.T.blockVacuumCoordinateEquiv_isometry D cc δ B n n' x y) hH _ _ _ _ hsc' hF0' hidx' z
  rw [GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels D cc δ B hS n n' z]
  congr 1
  rw [Iop_eq, GlobalTheory.T.blockVacuumLattice_eq_comap_standardLattice, GlobalTheory.T.la_tor0_stdL_eq_blkLat, show StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.tor0 D cc δ).abelian₂ (B.ω₀ / 2))
      = fun v => F0 B.L B.ω₀ (Ix D n n') (phi B n n' v) from funext (GlobalTheory.T.pullback_basis_theta_eq_F0_form D cc δ B n n')]
  rw [inter_congr_al _ _ (fun v => alphaQ B.cq (stdH B.L (Ix D n n')) (phi B n n' v)) _ _ _ ?_, hnat, hprod]
  · rfl
  · intro x hx
    have hx' : x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) := by
      rw [GlobalTheory.T.la_tor0_stdL_eq_blkLat D cc δ B n n']; exact hx
    obtain ⟨m, hm⟩ := B.qInt0 hS (n * 2) (n' * 2) x hx'
    rw [al_eq D _ x m hm]
    unfold alphaQ qOf
    rw [← GlobalTheory.T.blockVacuumCoordinateEquiv_isometry D cc δ B n n' x x]
    rfl

end GlobalTheory.BaseVacuum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaVectorIsVacuumEvenRanksStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.base_theta_vector_is_vacuum_even_ranks : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.kc.YFinite → ∀ N N' : ℕ, Even N → Even N' → StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) (B.ω₀ / 2) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') (B.thZero N N') := by
  first | exact @GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even | exact GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even | (intros; apply GlobalTheory.BaseVacuum.thetaVectorUpToUnits_thZero_of_even <;> assumption)
end
end
