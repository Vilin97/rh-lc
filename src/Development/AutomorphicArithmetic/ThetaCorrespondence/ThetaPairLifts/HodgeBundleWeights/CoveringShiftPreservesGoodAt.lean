module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShiftedWeightLatticeFg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponent
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivMulTwistingSectionIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistingSectionPreservesHermitianLatticesRanks
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodAtOfAntitoneGapWeight

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.ShiftGood

variable {D : D7} {T : Core D} {j : ℕ}

theorem cuspW_eq_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') : Y.V G = Y.V G' := by
  ext f
  rw [GlobalTheory.AllWt.mem_cuspW, GlobalTheory.AllWt.mem_cuspW, h]
  refine and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [GlobalTheory.AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) h]

theorem goodAt_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') (hG : Y.GoodAt G) : Y.GoodAt G' := by
  set_option synthInstance.maxHeartbeats 200000 in
  refine ⟨hasGram_nrm_of_good D T j Y e o hY G', ?_⟩
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((GlobalTheory.AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C : Set C) = ⊤) →
      ((GlobalTheory.AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C' : Set C') = ⊤) := by
    rintro C _ rfl; exact id
  exact key _ _ (cuspW_eq_of_exZ hY h) hG.2

end GlobalTheory.CovTop.ShiftGood

namespace GlobalTheory.CovTop.ShiftGood

end GlobalTheory.CovTop.ShiftGood

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.GenShift

open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_twPow (s : TwSec U x Z (wtOf Dw 0 1)) : ∀ n : ℕ, Nonempty (TwSec U x Z (wtOf Dw 0 (n : ℤ))) := by
  intro n
  induction n with
  | zero => exact ⟨(TwSec.const x s.pts 1 one_ne_zero).copy (by rw [Nat.cast_zero, wtOf_zero])⟩
  | succ n ih =>
    obtain ⟨t⟩ := ih
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero, Nat.cast_succ])⟩


set_option maxHeartbeats 1000000 in
theorem span_latW_add (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G G₀ : WTZ E) (hG : Even G.2)
    (hs : ∀ Z : Comp Xo c, Nonempty (TwSec U x Z G₀))
    (h : Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) = ⊤) :
    Submodule.span c.F (latW U (G + G₀) : Set (cuspW Xo c U (G + G₀))) = ⊤ := by
  classical
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [eq_top_iff]
  intro F _
  have hF : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF]
  refine Submodule.sum_mem _ fun Z _ => ?_
  obtain ⟨s⟩ := hs Z
  obtain ⟨φ, -, -, hA, -⟩ := GlobalTheory.FlatTw.Mul.twSec_mulEquiv_integral E H Dw l Xo c r U x Z G₀ s G hG
  obtain ⟨a, ha0, hlo, -⟩ := GlobalTheory.FlatTw.Good.exists_twist_scalar s
  let p : cuspOn U Z (G + G₀) := ⟨idem Z * (F : Rul Xo c),
    GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, by rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)⟩
  let g : cuspOn U Z G := φ.symm p
  have hmem : (⟨(g : Rul Xo c), g.2.1⟩ : cuspW Xo c U G) ∈ Submodule.span c.F (latW U G : Set (cuspW Xo c U G)) := by
    rw [h]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 c.F)) c.F _ _ hmem
  rw [Submodule.span_eq, Submonoid.smul_def, ← algebraMap_smul c.F] at ht
  set d : c.F := algebraMap (𝓞 c.F) c.F t with hd
  have hd0 : d ≠ 0 := by simpa [hd] using nonZeroDivisors.ne_zero t.2
  have hf : d • g ∈ latOn U Z G := (mem_latOn U).2 ht
  have hq := hA a ha0 hlo (d • g) hf ((a * d) • p) (by
    simp only [g, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, smul_smul])
  have hq' := (mem_latOn U).1 hq
  have had : a * d ≠ 0 := mul_ne_zero ha0 hd0
  have e : (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U (G + G₀)) =
      (a * d)⁻¹ • (⟨(((a * d) • p : cuspOn U Z (G + G₀)) : Rul Xo c), ((a * d) • p).2.1⟩ : cuspW Xo c U (G + G₀)) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_smul, inv_mul_cancel₀ had, one_smul, p]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hq')

end General

end GlobalTheory.GenShift
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightLatticeSpannedByWeights

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.GenShift
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}
end General
theorem span_weight_lattice_of_weights : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la m) : Set (Y.V (wtOf _ la m))) = ⊤ := by
  intro _ D T hT j hp _ _ hj Y e o hG la _ _ hgood m
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    Formalism.L2.Pj.goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0
  have hs : ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 (m : ℤ))) := fun Z => by
    obtain ⟨s⟩ := GlobalTheory.KeyTwDeep.twSec_keyRoot _ _ _ _ _ _ _ _ _ hG.unf hG.xiAbs hG.geo (le_add_right hp) hg Z
    exact exists_twPow s m
  have h0 := (hgood 0).2.2
  rw [zero_add, one_smul] at h0
  have key := span_latW_add hG.unf (wtOf (T.Q.Dw j) la 0) (wtOf (T.Q.Dw j) 0 (m : ℤ)) (even_wtOf _ _) hs h0
  have hGG : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) 0 (m : ℤ) = wtOf (T.Q.Dw j) la (m : ℤ) := by
    rw [← wtOf_add, add_zero, zero_add]
  rw [hGG] at key
  exact key
end GlobalTheory.GenShift
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.weight_lattice_spanned_by_weights : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → (∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • la) 0)) → ∀ m : ℕ, Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la m) : Set (Y.V (wtOf _ la m))) = ⊤ := by
  first | exact @_root_.GlobalTheory.GenShift.span_weight_lattice_of_weights | exact _root_.GlobalTheory.GenShift.span_weight_lattice_of_weights | (intros; apply _root_.GlobalTheory.GenShift.span_weight_lattice_of_weights <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt

section

@[expose] public section

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.ShiftGood
variable {D : D7} {T : Core D} {j : ℕ}
end GlobalTheory.CovTop.ShiftGood
namespace GlobalTheory.CovTop.ShiftGood
theorem covering_goodAt_shift : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  intro hP D T hT j hp hq hf hj Y e o hY a n s hn hA hg
  obtain ⟨m, rfl⟩ := hn
  have hmul : ∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • (laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j))) 0) := by
    intro k
    refine (_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY _ (fun τ => ?_) (fun τ => ?_)).1
    · intro x y hxy
      simp only [Pi.smul_apply]
      exact nsmul_le_nsmul_right (hA τ hxy) _
    · have := hg τ
      simp only [Pi.smul_apply]
      unfold gap at this ⊢
      split_ifs at this ⊢ with h1
      · simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        have hk : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos k
        rw [← mul_sub]
        exact this.trans (le_mul_of_one_le_left (by linarith) hk)
      · exact this
  refine goodAt_of_exZ hY ?_ ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _,
    _root_.GlobalTheory.T.shifted_weight_lattice_fg hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m,
    _root_.GlobalTheory.T.weight_lattice_spanned_by_weights hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m⟩
  rw [← two_mul, GlobalTheory.CovTop.Model.exZ_shiftG]
  rfl
end GlobalTheory.CovTop.ShiftGood
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.covering_shift_preserves_goodAt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  first | exact @_root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift | exact _root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift | (intros; apply _root_.GlobalTheory.CovTop.ShiftGood.covering_goodAt_shift <;> assumption)
end
end
end
