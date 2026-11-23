module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

-- Source module: PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacNeZero

section

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

theorem jac_ne_zero (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (x : V) (hx0 : x ≠ 0) (hx : x ∈ G.Eig π) :
    (Submodule.Quotient.mk x : Jacquet π (unipRad k G.e)) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := hun
  have hJmul' := hJmul hcb hccB
  have hJinv' := hJinv hcb hccB
  have hΔU' := hΔU hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  have hiw' := hiw hcb hccB hΔU hJmul hJinv
  have hTE' := hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  have hTI' := hTI hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V π hs
  have hTp' := hTp hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw hTE ϖ hϖ V π
  have hE : ∀ y ∈ G.Eig π, G.Tz π ϖ 1 y ∈ G.Eig π := fun y hy => (hTE' ϖ hϖ 1).2 V π y hy
  have key : ∀ m : ℕ, ∀ y ∈ G.Eig π, (G.Tz π ϖ 1)^[m] y = 0 → y = 0 := by
    intro m
    induction m with
    | zero => intro y _ h; simpa using h
    | succ m ih =>
      intro y hy h
      rw [Function.iterate_succ_apply] at h
      exact hTI' y hy (ih _ (hE y hy) h)
  intro h0
  obtain ⟨m, hm⟩ := hjK hcb hccB hΔU hΔM hJmul hJinv hlM hiw hTE hlU ϖ hϖ V π hs x hx h0
  rw [hTp' x hx m] at hm
  exact hx0 (key m x hx hm)

theorem cMain (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.JacquetProductProp) : G.CMainFor := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩

end Grp

end UpperTheory.TNZ
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCTop

section

@[expose] public section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem cMain_alt (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.Step_jacProd_alt) : G.CMainForAlt := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩
end Grp
end UpperTheory.TNZ
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJTop

section

@[expose] public section




section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem jacProd_of_alt (hjF : G.Step_jacFin_alt) (hsub : G.SubquotientProp) (hten : G.Step_tensor_alt) (hsupp : G.Step_suppProd_alt) :
    G.Step_jacProd_alt := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩
end Grp
def CStepsAlt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.Step_jacFin_alt ∧ G.SubquotientProp ∧ G.Step_tensor_alt ∧ G.Step_suppProd_alt
open UpperTheory.NonzeroTypeTheory in
theorem twisted_spherical_product_of_irreducible_of_eigenvector (hC : _root_.UpperTheory.TNZ.CStepsAlt) (hlL : LeviSubgroupRestriction) (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain_alt hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of_alt hjF hsub hten hsupp) L V ρ hs hi hx
open UpperTheory.NonzeroTypeTheory in
theorem need_CProps_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem
open UpperTheory.NonzeroTypeTheory in
theorem need_Grp_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩
end UpperTheory.TNZ
end
end
end
end
