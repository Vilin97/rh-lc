module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Algebra.Azumaya.Basic
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelFunctionFiniteRange

section

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.HalfLatFin

theorem isHalf_of_nsmul {D : D7} {m n : ℕ} (e : AE D) {N : ℕ} (hN : 0 < N) {t t' w : Mx D m n}
    (ht : IsHalf e t) (ht' : IsHalf e t') (hw : t = t' + N • w) : IsHalf e w := by
  intro i j
  have h0 : t i j = t' i j + N • w i j := by
    have := congrFun (congrFun hw i) j
    simpa using this
  have hw' : N • w i j = t i j - t' i j := by rw [h0]; abel
  have h1 : (N : D.host.F) • (e * w i j - w i j) = 0 := by
    rw [Nat.cast_smul_eq_nsmul, smul_sub, ← mul_smul_comm, hw', mul_sub, ht i j, ht' i j, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left (by exact_mod_cast hN.ne'))

end GlobalTheory.HalfLatFin

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteRepsHalfStandardHomModNsmul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section



namespace GlobalTheory.HalfStdFin

theorem exists_reps_half_stdHom : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ stdHom S T, IsHalf E₂ u → ∃ r ∈ R, ∃ v ∈ stdHom S T, IsHalf E₂ v ∧ u = r + k • v := by
  classical
  intro D S T Q E₂ _ k hk
  obtain ⟨R, hR, h⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T (Formalism.L2.Col.stdLat D.host.E S.rank)
    (Formalism.L2.Col.stdLat D.host.E T.rank) (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := S.rank)).fg
    (Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := T.rank)).fg (fun _ => True) k hk
  rw [coe_colStdLat, coe_colStdLat] at h
  let G : WO S T → Prop := fun r => ∃ u ∈ stdHom S T, IsHalf E₂ u ∧ ∃ w ∈ stdHom S T, u = r + k • w
  let pick : WO S T → WO S T := fun r => if hG : G r then hG.choose else 0
  refine ⟨hR.toFinset.image pick, fun u hu hh => ?_⟩
  obtain ⟨r, hr, w, hw, huw⟩ := h u hu
  have hG : G r := ⟨u, hu, hh, w, hw, huw⟩
  obtain ⟨_, hh₀, w₀, hw₀, hu₀w⟩ := hG.choose_spec
  have hp : pick r = hG.choose := dif_pos hG
  have hdiff : u = hG.choose + k • (w - w₀) := by
    rw [hu₀w, smul_sub, huw]; abel
  exact ⟨pick r, Finset.mem_image_of_mem _ (hR.mem_toFinset.2 hr), w - w₀, sub_mem hw hw₀,
    GlobalTheory.HalfLatFin.isHalf_of_nsmul E₂ hk hh hh₀ hdiff, by rw [hp]; exact hdiff⟩

end GlobalTheory.HalfStdFin

end
end
end
