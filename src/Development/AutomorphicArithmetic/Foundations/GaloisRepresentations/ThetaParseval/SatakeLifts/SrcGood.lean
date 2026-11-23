module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTransposeInvTranspose

section

@[expose] public section

noncomputable section

namespace GlobalTheory.InvTransposeEnds

section General

variable {G H V W Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_comp {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (φ : H →* G)
    (hφ : Function.Surjective φ) : Representation.IsIrreducible (ρ.comp φ) := by
  haveI hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := hφ g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases h.eq_bot_or_eq_top S' with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))

end General

end GlobalTheory.InvTransposeEnds
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcGood

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.srcGood :
    UpperTheory.Gal.TP.Loc.SrcGood := by
  intro k _ _ _ _ n c V _ _ σ hc hu hs hirr hun
  have hcont : Continuous (GlobalTheory.SplitFlip.invT : GL (Fin n) k →* GL (Fin n) k) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun h : GL (Fin n) k => ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_coe_inv.matrix_transpose
    · show Continuous fun h : GL (Fin n) k => (h : Matrix (Fin n) (Fin n) k).transpose
      exact Units.continuous_val.matrix_transpose
  refine ⟨?_, ?_, ?_⟩
  · exact isSmooth_twist (isSmooth_comp hs _ hcont) hc.detChar
  · have ht {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
        {ρ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (χ : G →* ℂˣ) :
        (twist ρ χ).IsIrreducible := by
      let e : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have h := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          simpa [twist_apply, smul_smul] using h⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
      exact e.isSimpleOrder_iff.2 hρ
    exact ht (GlobalTheory.InvTransposeEnds.isIrreducible_comp hirr _
      fun h => ⟨GlobalTheory.SplitFlip.invT h, GlobalTheory.SplitFlip.invT_invT h⟩) _
  · obtain ⟨B, h1, h2, h3⟩ := hun
    refine ⟨B, h1, h2, fun g v w => ?_⟩
    rw [src_apply, src_apply, LinearMap.map_smul B, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have hn := hu (Matrix.GeneralLinearGroup.det g)
    rw [show ((c (Matrix.GeneralLinearGroup.det g) : ℂ) * (starRingEnd ℂ) (c (Matrix.GeneralLinearGroup.det g) : ℂ)) = 1 by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num, one_mul]
end
end
