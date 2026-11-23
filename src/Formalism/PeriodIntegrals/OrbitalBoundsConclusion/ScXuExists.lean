module

public import Formalism.PeriodIntegrals.ScXuExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.GlueHoldsVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LinMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.NatCastTmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.ValNatCastLtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalDataSatisfyLinearHypotheses
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitIso
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.RingTheory.Valuation.AlgebraInstances
public import Mathlib.RingTheory.Valuation.Integral
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitUnitaryProjectionCompatibility

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocalIdempotentExistence

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

def smulLin (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : RV I v) :
    (Fin I.n → RV I v) →ₗ[OV I v] (Fin I.n → RV I v) where
  toFun x := c • x
  map_add' x y := smul_add c x y
  map_smul' o x := by
    simp only [RingHom.id_apply]
    rw [PI.FinKW.LocTo.ov_smul_vec, PI.FinKW.LocTo.ov_smul_vec, smul_comm]

theorem idem_kill (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (g : ℕ) (hg : (g : 𝓞 I.F) ∈ v.asIdeal)
    (c : RV I v) (hcc : c * c = c)
    (hc : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = (g : RV I v) • w) :
    ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0 := by
  have hfg : ((Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c)).FG :=
    (latLoc_fg I v).map _
  have hle : (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) ≤
      Ideal.span {(g : OV I v)} • (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hcw⟩ := hc x hx
    have e : (smulLin I v c) x = (g : OV I v) • (smulLin I v c w) := by
      show c • x = (g : OV I v) • (c • w)
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (RV I v), smul_comm, ← hcw, smul_smul, hcc]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (Submodule.mem_map_of_mem hw)
  have hjac : Ideal.span {(g : OV I v)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_max I.F v g hg
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac
  intro x hx
  have hm : (smulLin I v c) x ∈ (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) :=
    Submodule.mem_map_of_mem hx
  rw [hbot, Submodule.mem_bot] at hm
  exact hm

theorem kill_zero (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (hn : 0 < I.n) (c : RV I v)
    (h : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0) : c = 0 := by
  have key : ∀ x ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E)),
      c • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [PI.FinKW.ratV_zero', smul_zero]
    | add y z _ _ hy hz => rw [PI.FinKW.ratV_add', smul_add, hy, hz, add_zero]
    | smul a y _ hy =>
      have e : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (a • y) =
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) a) •
            Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) y := by
        funext i
        simp only [Formalism.L2.SG.Sub.ratV, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [e, smul_comm, hy, smul_zero]
  have h0 := key (Pi.single ⟨0, hn⟩ 1) (by rw [I.L_span]; exact Submodule.mem_top)
  have e1 : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Pi.single ⟨0, hn⟩ (1 : I.E)) =
      Pi.single ⟨0, hn⟩ 1 := by
    funext i
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simp [Formalism.L2.SG.Sub.ratV]
    · simp [Formalism.L2.SG.Sub.ratV, hi]
  rw [e1] at h0
  have h1 := congrFun h0 ⟨0, hn⟩
  simpa using h1

theorem local_idempotent_existence : LocIdem := by
  intro I g r k e f Rf hg hn v hv
  have hb : PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) *
      PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) =
      PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
    rw [← map_mul, eps_idem Rf v]
  have hcc : (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) *
      (1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew)) =
      1 - PI.FinKW.psiV I v Rf.ew - PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
    linear_combination eps_idem Rf v + hb + 2 * eps_orth Rf v
  have hkill := idem_kill I v g hv _ hcc (fun x hx => full_loc Rf v x hx)
  have hz := kill_zero I v (by omega) _ hkill
  linear_combination -hz

end PI.UnitaryGroupMassFormula.ScXuExists
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Assemble

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

theorem scXuExists_of (hS : LocSplitP) (hA : BridgeA) (hB : BridgeB) : _root_.PI.ScXuExists.Target :=
  target_of' local_idempotent_existence hS hA hB existsLatticeAutomorphismApprox Gl.glue_holds_var

end PI.UnitaryGroupMassFormula.ScXuExists
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitGen

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open scoped TensorProduct
open PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem exists_adapted_first_projection (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0) (ε : K ⊗[F] E) (hsum : ε + sigT σ ε = 1) (horth : ε * sigT σ ε = 0) :
    ∃ p1 : K ⊗[F] E →+* K, (∀ c : K, p1 (algebraMap K (K ⊗[F] E) c) = c) ∧ p1 ε = 1 ∧
      p1 (sigT σ ε) = 0 ∧
      ∀ r : K ⊗[F] E, r = algebraMap K (K ⊗[F] E) (p1 r) * ε +
        algebraMap K (K ⊗[F] E) (p1 (sigT σ r)) * sigT σ ε := by
  classical
  have hσT : ∀ x : K ⊗[F] E, sigT σ (sigT σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [sigT, hσσ]
    | add x y hx hy => simp [map_add (f := _), hx, hy]
  have hσA : ∀ c : K, sigT σ (algebraMap K (K ⊗[F] E) c) = algebraMap K (K ⊗[F] E) c := by
    intro c
    simp [sigT, Algebra.TensorProduct.algebraMap_apply]
  have hε2 : ε * ε = ε := by
    calc ε * ε = ε * (ε + sigT σ ε) - ε * sigT σ ε := by ring
      _ = ε := by rw [hsum, horth, mul_one, sub_zero]
  have hfr : Module.finrank K (K ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, h2]
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K (K ⊗[F] E) := inferInstance
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, map_zero, add_zero] at hsum
    exact zero_ne_one hsum
  have hδ0 : sigT σ ε ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hsum
    rw [hsum, map_one] at h0
    exact one_ne_zero h0
  have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.mulRight K ε)
  rw [hfr] at hrn
  have hker : Module.finrank K (LinearMap.ker (LinearMap.mulRight K ε)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro h
    apply hδ0
    apply h
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_comm, horth]
  have hmemε : ε ∈ LinearMap.range (LinearMap.mulRight K ε) :=
    ⟨ε, by rw [LinearMap.mulRight_apply, hε2]⟩
  have hran : Module.finrank K (LinearMap.range (LinearMap.mulRight K ε)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro h
    exact hε0 (h ε hmemε)
  have h1 : Module.finrank K (LinearMap.range (LinearMap.mulRight K ε)) = 1 := by omega
  have hex : ∀ r : K ⊗[F] E, ∃ c : K, algebraMap K (K ⊗[F] E) c * ε = r * ε := by
    intro r
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨ε, hmemε⟩ : LinearMap.range (LinearMap.mulRight K ε))
      (fun h => hε0 (congrArg Subtype.val h))).mp h1 ⟨r * ε, ⟨r, rfl⟩⟩
    refine ⟨c, ?_⟩
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  have huniq : ∀ c d : K, algebraMap K (K ⊗[F] E) c * ε = algebraMap K (K ⊗[F] E) d * ε →
      c = d := by
    intro c d h
    rw [← Algebra.smul_def, ← Algebra.smul_def, ← sub_eq_zero, ← sub_smul] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hε0)
  choose p hp using hex
  have hpu : ∀ r c, algebraMap K (K ⊗[F] E) c * ε = r * ε → p r = c :=
    fun r c h => huniq _ _ ((hp r).trans h.symm)
  let p1 : K ⊗[F] E →+* K :=
    { toFun := p
      map_one' := hpu 1 1 (by rw [map_one])
      map_mul' := fun r s => hpu (r * s) (p r * p s) (by
        rw [map_mul, mul_assoc, hp s, mul_left_comm, hp r, ← mul_assoc, mul_comm s r])
      map_zero' := hpu 0 0 (by rw [map_zero])
      map_add' := fun r s => hpu (r + s) (p r + p s) (by
        rw [map_add (f := _), add_mul, hp r, hp s, add_mul]) }
  refine ⟨p1, fun c => hpu _ c rfl, hpu _ 1 (by rw [map_one, one_mul, hε2]),
    hpu _ 0 (by rw [map_zero, zero_mul, mul_comm, horth]), fun r => ?_⟩
  have h2' : algebraMap K (K ⊗[F] E) (p (sigT σ r)) * sigT σ ε = r * sigT σ ε := by
    have h3 : sigT σ (algebraMap K (K ⊗[F] E) (p (sigT σ r)) * ε) = sigT σ (sigT σ r * ε) := by
      rw [hp (sigT σ r)]
    rwa [map_mul, map_mul, hσA, hσT] at h3
  show r = algebraMap K _ (p r) * ε + algebraMap K _ (p (sigT σ r)) * sigT σ ε
  rw [hp r, h2', ← mul_add, hsum, mul_one]

end PI.UnitaryGroupMassFormula.ScXuExists
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.SplitLoc

section

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem locSplitP_dec (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f)
    (v : HeightOneSpectrum (𝓞 I.F)) (hsum : SumOne I v (PI.FinKW.psiV I v Rf.ew)) :
    ∃ p1 : RV I v →+* KV I v, IsAdaptedFirstProjection I v (PI.FinKW.psiV I v Rf.ew) p1 ∧
      ∀ x : RV I v, x = algebraMap (KV I v) (RV I v) (p1 x) * PI.FinKW.psiV I v Rf.ew +
        algebraMap (KV I v) (RV I v) (p1 (PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v x)) *
          PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) := by
  have : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v)).injective
  have h2K : (2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ≠ 0 := two_ne_zero
  obtain ⟨p1, h1, h2, h3, h4⟩ := exists_adapted_first_projection (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_sig I) (PI.UnitaryGroupMassFormula.AdIndexEq.spl_sig_fix I) I.cm.deg2 h2K
    (PI.FinKW.psiV I v Rf.ew) hsum (eps_orth Rf v)
  refine ⟨p1, ⟨h1, h2, h3, ?_⟩, h4⟩
  rintro x ⟨z, rfl⟩
  obtain ⟨fp, hm, hf⟩ := NumberField.RingOfIntegers.isIntegral_coe z
  have hf' : Polynomial.eval₂ (algebraMap ℤ I.E) (algebraMap (𝓞 I.E) I.E z) fp = 0 := hf
  show (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)) (algebraMap (𝓞 I.E) I.E z) ∈ OV I v
  refine (Valuation.valuationSubring.integers (Valued.v (R := v.adicCompletion I.F))).mem_of_integral
    ⟨fp.map (Int.castRingHom _), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hc : (algebraMap (Valued.v (R := v.adicCompletion I.F)).valuationSubring (v.adicCompletion I.F)).comp
      (Int.castRingHom (Valued.v (R := v.adicCompletion I.F)).valuationSubring) =
      (p1.comp (PI.UnitaryGroupMassFormula.AdIndexEq.inclV I v)).comp (algebraMap ℤ I.E) := RingHom.ext_int _ _
  rw [hc, ← Polynomial.hom_eval₂, hf', map_zero]

theorem local_splitting_projection : LocSplitP := by
  intro I g r k e f Rf v hsum
  obtain ⟨p1, hp, -⟩ := locSplitP_dec I g r k e f Rf v hsum
  exact ⟨p1, hp⟩

end PI.UnitaryGroupMassFormula.ScXuExists
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScXuExists

section

@[expose] public section

theorem sc_xu_exists : PI.ScXuExists.Target :=
  PI.UnitaryGroupMassFormula.ScXuExists.scXuExists_of PI.UnitaryGroupMassFormula.ScXuExists.local_splitting_projection
    PI.UnitaryGroupMassFormula.ScXuExists.BrA.local_data_satisfy_linear_hypotheses PI.UnitaryGroupMassFormula.ScXuExists.BrB.split_unitary_projection_compatibility
end
end
