module

public import Formalism.LocalRingCardinality.DataArith
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.SharpRestriction.Divisibility.HookProducts.RBTieOp
public import Formalism.HarderNarasimhan.Statement
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.Divisibility.HookProducts.RBTieFrame

-- Source module: Formalism.SharpRestriction.Divisibility.HookProducts.RBTieSlope

section

@[expose] public section

open Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

theorem slope_eq_of_norm_eq {R V E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ₂ : V →+ F) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (N : Submodule R V) :
    Formalism.HN.slope ρ₂ N = Formalism.HN.slope ρ N := by
  classical
  have memL : ∀ y : E, y ∈ Formalism.HN.zl ρ N ↔ ∃ x ∈ N.toAddSubgroup, ρ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ) ↔ _
    exact AddSubgroup.mem_map
  have memM : ∀ y : F, y ∈ Formalism.HN.zl ρ₂ N ↔ ∃ x ∈ N.toAddSubgroup, ρ₂ x = y := by
    intro y
    show y ∈ (N.toAddSubgroup.map ρ₂) ↔ _
    exact AddSubgroup.mem_map
  let pre : Formalism.HN.zl ρ N → V := fun y => Classical.choose ((memL y).1 y.2)
  have pre_mem : ∀ y, pre y ∈ N.toAddSubgroup := fun y =>
    (Classical.choose_spec ((memL y).1 y.2)).1
  have pre_eq : ∀ y, ρ (pre y) = y := fun y => (Classical.choose_spec ((memL y).1 y.2)).2
  let f0 : Formalism.HN.zl ρ N →+ Formalism.HN.zl ρ₂ N :=
    AddMonoidHom.mk' (fun y => ⟨ρ₂ (pre y), (memM _).2 ⟨pre y, pre_mem y, rfl⟩⟩) (by
      intro y z
      apply Subtype.ext
      show ρ₂ (pre (y + z)) = ρ₂ (pre y) + ρ₂ (pre z)
      rw [← map_add (f := _)]
      apply Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn
      rw [map_add (f := _), pre_eq, pre_eq, pre_eq]
      rfl)
  have f0_apply : ∀ y, ((f0 y : Formalism.HN.zl ρ₂ N) : F) = ρ₂ (pre y) := fun y => rfl
  have f0_norm : ∀ y, ‖((f0 y : Formalism.HN.zl ρ₂ N) : F)‖ = ‖(y : E)‖ := by
    intro y
    rw [f0_apply, hn, pre_eq]
  have hinj : Function.Injective f0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h0 : ‖(y : E)‖ = 0 := by
      rw [← f0_norm, hy]
      simp
    exact Subtype.ext (norm_eq_zero.1 h0)
  have hsurj : Function.Surjective f0 := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := (memM z).1 hz
    refine ⟨⟨ρ x, (memL _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    rw [f0_apply]
    exact Formalism.HN.Rerealization.eq_of_eq ρ ρ₂ hn (pre_eq _)
  let e : Formalism.HN.zl ρ N ≃+ Formalism.HN.zl ρ₂ N := AddEquiv.ofBijective f0 ⟨hinj, hsurj⟩
  have e_norm : ∀ y, ‖e y‖ = ‖y‖ := fun y => f0_norm y
  have e_symm_norm : ∀ z, ‖e.symm z‖ = ‖z‖ := by
    intro z
    rw [← e_norm (e.symm z), e.apply_symm_apply]
  have iso : Isometry e := AddMonoidHomClass.isometry_of_norm e e_norm
  have iso_symm : Isometry e.symm := AddMonoidHomClass.isometry_of_norm e.symm e_symm_norm
  have hiff : DiscreteTopology (Formalism.HN.zl ρ N) ↔ DiscreteTopology (Formalism.HN.zl ρ₂ N) := by
    constructor
    · intro h
      exact iso_symm.isEmbedding.discreteTopology
    · intro h
      exact iso.isEmbedding.discreteTopology
  have hrk : Formalism.F.rk (Formalism.HN.zl ρ₂ N) = Formalism.F.rk (Formalism.HN.zl ρ N) := by
    unfold Formalism.F.rk
    exact e.toIntLinearEquiv.finrank_eq.symm
  have hcov : Formalism.F.covol (Formalism.HN.zl ρ₂ N) = Formalism.F.covol (Formalism.HN.zl ρ N) := by
    by_cases h : DiscreteTopology (Formalism.HN.zl ρ N)
    · exact (Formalism.HN.Rerealization.covol_rk_eq ρ ρ₂ hn N.toAddSubgroup h (hiff.1 h)).1
    · have h' : ¬ DiscreteTopology (Formalism.HN.zl ρ₂ N) := fun h' => h (hiff.2 h')
      unfold Formalism.F.covol
      rw [dite_eq_right h, dite_eq_right h']
  unfold Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [hcov, hrk]

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.HookProducts.RBTieMu

section

@[expose] public section

open Matrix NumberField Module

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBTie

section Mu

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mem_dualLat_iff {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (A : Submodule (𝓞 K) V) (f : Module.Dual K V) :
    f ∈ Formalism.HN.dualLat A ↔ ∀ x ∈ A, f x ∈ Set.range (algebraMap (𝓞 K) K) := Iff.rfl

theorem cnorm_isom {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (W : Matrix m n ℂ)
    (hW : Wᴴ * W = 1) (c : n → ℂ) : Formalism.HermitianLatticesTheory.cnorm (W *ᵥ c) = Formalism.HermitianLatticesTheory.cnorm c := by
  have key : ∀ {ι : Type} [Fintype ι] (u : ι → ℂ), ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
    intro ι _ u
    push_cast
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have h : ((∑ i, ‖(W *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [key, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hW,
      Matrix.one_mulVec]
  exact_mod_cast h

theorem muDual_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y)
    (hXA : ∀ v, IsUnit (A.X v).det) (hXE : ∀ v, IsUnit (XE v).det) :
    Formalism.HN.muDef (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat L) = A.muDual := by
  set ψ : Module.Dual K (Fin n → K) →ₗ[K] Module.Dual K A.V := Module.Dual.transpose e.symm.toLinearMap with hψ
  have hψx : ∀ f x, ψ f x = f (e.symm x) := fun f x => by simp [hψ, Module.Dual.transpose_apply]

  have hnA : ∀ v f, Formalism.HermitianLatticesTheory.normAt A.b.dualBasis (Formalism.HN.dualFrame A.X) v (ψ f) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) v f := by
    intro v f
    have hv := vecAt_map (Pi.basisFun K (Fin n)).dualBasis A.b.dualBasis v ψ f
    have hT : LinearMap.toMatrix (Pi.basisFun K (Fin n)).dualBasis A.b.dualBasis ψ =
        (LinearMap.toMatrix A.b (Pi.basisFun K (Fin n)) e.symm.toLinearMap)ᵀ := by
      rw [hψ, LinearMap.toMatrix_transpose]
    have hW : ((A.X v)ᵀ * (cQ A.b e v)ᵀ) = ((cU A.b A.X XE e v)ᴴ)ᵀ * (XE v)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, cQ_mul_XA A.b A.X XE e v hmet (hXA v) (hXE v)]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
    rw [hv, hT, dualFrame_inv A.X v (hXA v), dualFrame_inv XE v (hXE v), Matrix.mulVec_mulVec]
    have hQ : (LinearMap.toMatrix A.b (Pi.basisFun K (Fin n)) e.symm.toLinearMap)ᵀ.map v.embedding = (cQ A.b e v)ᵀ := rfl
    rw [hQ, hW, ← Matrix.mulVec_mulVec, cnorm_isom]
    rw [conjT_transpose_isom, cU_conj_mul A.b A.X XE e v hmet (hXE v), Matrix.transpose_one]
  have hn : ∀ f, ‖((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) f‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) f‖ := by
    intro f
    have h2 : ‖((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) f‖ ^ 2 =
        ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE) f‖ ^ 2 := by
      rw [AddMonoidHom.comp_apply, Formalism.HN.PlaceOperatorNorms.norm_sq_realize, Formalism.HN.PlaceOperatorNorms.norm_sq_realize]
      simp only [LinearMap.toAddMonoidHom_coe, hnA]
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq (norm_nonneg _)]

  have hzl : Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)) (Formalism.HN.dualLat A.L) =
      Formalism.HN.zl ((Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)).comp ψ.toAddMonoidHom) (Formalism.HN.dualLat L) := by
    ext y
    rw [Formalism.HN.satR_mem_zl, Formalism.HN.satR_mem_zl]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨Module.Dual.transpose e.toLinearMap g, ?_, ?_⟩
      · rw [mem_dualLat_iff] at hg ⊢
        intro x hx
        simp only [Module.Dual.transpose_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        exact hg (e x) (by rw [hlat]; exact ⟨x, hx, rfl⟩)
      · congr 1
        exact LinearMap.ext fun x => by simp [hψx, Module.Dual.transpose_apply]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨ψ f, ?_, rfl⟩
      rw [mem_dualLat_iff] at hf ⊢
      intro z hz
      rw [hlat] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [hψx]
      simpa using hf x hx
  have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b.dualBasis (Formalism.HN.dualFrame A.X)) (Formalism.HN.dualLat A.L) =
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame XE)) (Formalism.HN.dualLat L) := by
    rw [← slope_eq_of_norm_eq _ _ hn (Formalism.HN.dualLat L)]
    unfold Formalism.HN.slope
    rw [hzl]
  unfold Formalism.BasicNotions.HLat.muDual Formalism.BasicNotions.HLat.dualB Formalism.BasicNotions.HLat.dualX Formalism.BasicNotions.HLat.dualL Formalism.HN.muDef
  rw [hs]

end Mu

end Formalism.MainNotions.DIV.HookProducts.RBTie
end
end
end
