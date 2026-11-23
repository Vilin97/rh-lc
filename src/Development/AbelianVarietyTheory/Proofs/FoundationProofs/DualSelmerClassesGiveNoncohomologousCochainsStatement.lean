module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonalStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonalStatement
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDualStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMap

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.SelPerp

theorem coef_free_pairSurj (l : ℕ) [Fact l.Prime] (c : Coef l) : Module.Free ℤ_[l] c.O := by
  haveI : Module.IsTorsionFree ℤ_[l] c.O := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun a x h => ?_
    have h' : a • (x : Qbar l) = 0 := by rw [← Subalgebra.coe_smul, h]; rfl
    rw [Algebra.smul_def, mul_eq_zero] at h'
    rcases h' with h' | h'
    · left
      have := congrArg norm h'
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap', norm_zero] at this
      have h2 : ((a : ℤ_[l]) : ℚ_[l]) = 0 := norm_eq_zero.1 this
      exact PadicInt.coe_eq_zero.1 h2
    · right
      exact Subtype.ext h'
  infer_instance

theorem exists_eq_tbA_mul (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)) :
    ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  classical
  haveI := coef_free_pairSurj l c
  let e := Module.Free.chooseBasis ℤ_[l] c.O
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := e.constr ℤ_[l] fun i => (((φ (red c n (e i))).val : ℕ) : ℤ_[l])
  have hf : ∀ x : c.O, PadicInt.toZModPow n (f x) = φ (red c n x) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp only [f, Module.Basis.constr_basis]
      rw [map_natCast, ZMod.natCast_zmod_val]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | smul a x _ hx =>
      rw [map_smul, smul_eq_mul, map_mul, hx, red_smul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  obtain ⟨b, hb, -⟩ := tau_spec c f
  refine ⟨red c n b, fun a => ?_⟩
  obtain ⟨x, rfl⟩ := red_surjective c n a
  rw [← hf, hb, ← map_mul, tbA_red, mul_comm]

end GlobalTheory.Ord2.SelPerp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqOrdDualGeneratorPairingOfAdditiveMapStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (φ : Qn c n →+ ZMod (l ^ n)), ∃ b : Qn c n, ∀ a : Qn c n, φ a = GlobalTheory.Ord2.SelPerp.tbA c n (a * b) := by
  first | exact @GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | exact GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul | (intros; apply GlobalTheory.Ord2.SelPerp.exists_eq_tbA_mul <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | exact GlobalTheory.Ord2.SelPerp.coef_free_pairSurj | (intros; apply GlobalTheory.Ord2.SelPerp.coef_free_pairSurj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerate

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

theorem tau_mul_dvd (c : Coef l) (n : ℕ) (b' : c.O)
    (h : ∀ a : Qn c n, tbA c n (a * red c n b') = 0) (x : c.O) :
    ∃ q : ℤ_[l], tau c (b' * x) = (l : ℤ_[l]) ^ n * q := by
  have h1 := h (red c n x)
  rw [← map_mul, tbA_red, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  rw [mul_comm]
  exact h1

theorem pair_nondeg (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n)
    (h : ∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) : b = 0 := by
  obtain ⟨b', rfl⟩ := red_surjective c n b
  have hd := tau_mul_dvd c n b' h
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let q : c.O → ℤ_[l] := fun x => Classical.choose (hd x)
  have hq : ∀ x, tau c (b' * x) = (l : ℤ_[l]) ^ n * q x := fun x => Classical.choose_spec (hd x)
  let g : c.O →ₗ[ℤ_[l]] ℤ_[l] :=
    { toFun := q
      map_add' := fun x y => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_add, map_add (f := _), hq, hq, mul_add]
      map_smul' := fun r x => by
        apply mul_left_cancel₀ hl
        rw [← hq, mul_smul_comm, map_smul, hq, RingHom.id_apply, smul_eq_mul, smul_eq_mul]
        ring }
  obtain ⟨a0, ha0⟩ := (tau_spec c g).exists
  let f : c.O →ₗ[ℤ_[l]] ℤ_[l] := (tau c).comp (LinearMap.mulLeft ℤ_[l] b')
  have e1 : ∀ x, f x = tau c (b' * x) := fun x => rfl
  have e2 : ∀ x, f x = tau c ((((l : ℤ_[l]) ^ n) • a0) * x) := fun x => by
    rw [e1, hq, smul_mul_assoc, map_smul, smul_eq_mul]
    congr 1
    exact ha0 x
  have heq : b' = ((l : ℤ_[l]) ^ n) • a0 := (tau_spec c f).unique e1 e2
  rw [heq, red_eq_zero_iff_mem]
  exact smul_mem_Ik c n (Ideal.mem_span_singleton_self _) a0

end GlobalTheory.Ord2.SelPerp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdDualGeneratorPairingModPowNondegenerateStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (b : Qn c n), (∀ a : Qn c n, GlobalTheory.Ord2.SelPerp.tbA c n (a * b) = 0) → b = 0 := by
  first | exact @GlobalTheory.Ord2.SelPerp.pair_nondeg | exact GlobalTheory.Ord2.SelPerp.pair_nondeg | (intros; apply GlobalTheory.Ord2.SelPerp.pair_nondeg <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.tau_mul_dvd | exact GlobalTheory.Ord2.SelPerp.tau_mul_dvd | (intros; apply GlobalTheory.Ord2.SelPerp.tau_mul_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochains

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section
namespace GlobalTheory.Ord2.SelPerp

theorem phi_bijective : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ), Function.Bijective (GlobalTheory.Ord2.SelPerp.Phi c n) := by
  intro l _ c n
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h : ∀ x : Mn c n, tbA c n (x 0 * y 1 - x 1 * y 0) = 0 := fun x : Mn c n => by
      rw [← Phi_apply, hy]; rfl
    have h1 : y 1 = 0 := GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun a => by simpa using h (Pi.single 0 a)
    have h0 : y 0 = 0 := GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun a => by simpa using h (Pi.single 1 (-a))
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · intro φ
    let φ' : Mn c n →ₗ[ZMod (l ^ n)] ZMod (l ^ n) := φ
    obtain ⟨b0, h0⟩ := GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap l c n (φ'.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 0))
    obtain ⟨b1, h1⟩ := GlobalTheory.T.exists_eq_ordDualGeneratorPairing_of_additiveMap l c n (φ'.toAddMonoidHom.comp (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 1))
    refine ⟨![-b1, b0], ?_⟩
    apply LinearMap.ext
    intro x
    change Phi c n ![-b1, b0] x = φ x
    have e : x = Pi.single 0 (x 0) + Pi.single 1 (x 1) := by
      funext i; fin_cases i <;> simp
    have e2 : φ x = φ' (Pi.single 0 (x 0)) + φ' (Pi.single 1 (x 1)) := by
      rw [← map_add (f := _), ← e]; rfl
    have h0' : φ' (Pi.single 0 (x 0)) = tbA c n (x 0 * b0) := h0 (x 0)
    have h1' : φ' (Pi.single 1 (x 1)) = tbA c n (x 1 * b1) := h1 (x 1)
    rw [Phi_apply, e2, h0', h1', ← map_add (f := _)]
    congr 1
    simp

theorem ord_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∀ y : G ℚ Ω → Mn c n, (∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) B), GlobalTheory.Ord2.SelPerp.Phi c n (y s) = f.1 ⟨s, hs⟩) → ∃ m : Qn c n, ∀ s ∈ Dec (F := ℚ) B, y s 1 = matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s 1 1 * m - m := by
  intro hL l _ Ω _ _ _ c n hn W hint hdet hcont S hN μ hμ B v hB hup f hf y hy
  obtain ⟨m, hm⟩ := GlobalTheory.T.dualCocycle_coboundary_on_stableLine_of_orthogonal hL l Ω c n hn W hint hcont S hN μ hμ B v hB hup f hf
  obtain ⟨w, rfl⟩ := (phi_bijective l c n).2 m
  refine ⟨w 1, fun s hs => ?_⟩
  have h10 : matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s 1 0 = 0 := by
    rw [matQ_apply, ← map_zero (red c n)]
    congr 1
    apply Subtype.ext
    show mat (dual1 W) s 1 0 = 0
    rw [CupCob.mat_dual1 W hdet, Matrix.smul_apply, hup s hs, smul_zero]
  rw [← sub_eq_zero]
  refine GlobalTheory.T.ordDualGeneratorPairing_modPow_nondegenerate l c n _ fun u => ?_
  have h := hm ⟨s, hs⟩ u
  have e := GlobalTheory.T.planePairing_equivariant_twist_cartierDual l Ω c n W hint hdet S hN μ hμ s w
  have e' : twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B ⟨s, hs⟩) (Phi c n w) =
      Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ w) := e.symm
  rw [← hy s hs, e', Phi_apply, Phi_apply, Phi_apply, ← map_sub, ← sub_eq_zero, ← map_sub] at h
  rw [← h]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10, Pi.single_eq_same, ne_eq, one_ne_zero,
    not_false_eq_true, Pi.single_eq_of_ne]
  ring



theorem sel_perp : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ, μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∃ z : SelD c n W hint S hN A hW.cont μ → (G ℚ Ω → Fin 2 → Qbar l), (∀ x, GwCount.SelN c n S A (dual1 W) (z x)) ∧ ∀ x x', x ≠ x' → ¬ Cob1 c n (dual1 W) ⊤ (z x - z x') := by
  intro hL l _ Ω _ _ _ e S A W hW c hint hN n hn μ hμ
  have hdet := hW.det2
  have hint' := CupCob.dual_representation_integral c W hdet hint
  have hbij : Function.Bijective (Phi c n) := phi_bijective l c n
  set E := LinearEquiv.ofBijective (Phi c n) hbij with hE
  have hΦΨ : ∀ φ, Phi c n (E.symm φ) = φ := fun φ => E.apply_symm_apply φ
  have heq := GlobalTheory.T.planePairing_equivariant_twist_cartierDual l Ω c n W hint hdet S hN μ hμ
  have hΨeq : ∀ s φ, E.symm (twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) φ) =
      matQ c n (dual1 W) hint' s *ᵥ E.symm φ := by
    intro s φ
    apply hbij.1
    rw [hΦΨ, heq, hΦΨ]
  set rho := rhoS c n W hint S hN with hrho_def
  have hcA : ContAction rho := contAction_rhoS c n W hint S hN hW.cont
  let rep : SelD c n W hint S hN A hW.cont μ → Z1 (twDual μ rho) :=
    fun x => Function.surjInv (Submodule.mkQ_surjective _) x.1
  have hrep : ∀ x, Submodule.mkQ _ (rep x) = x.1 := fun x => Function.surjInv_eq (Submodule.mkQ_surjective _) x.1
  let Y : SelD c n W hint S hN A hW.cont μ → G ℚ Ω → Mn c n := fun x s => E.symm ((rep x).1 (toGS Ω (S : Set Pl) s))
  have hY : ∀ x s, Phi c n (Y x s) = (rep x).1 (toGS Ω (S : Set Pl) s) := fun x s => hΦΨ _
  have hYc : ∀ x s t, Y x (s * t) = Y x s + matQ c n (dual1 W) hint' s *ᵥ Y x t := by
    intro x s t
    simp only [Y, map_mul, (rep x).2.2, map_add (f := _), hΨeq]
  refine ⟨fun x s => lftV c n (Y x s), fun x => ?_, fun x x' hne hcob => ?_⟩
  · have hsel0 := (mem_Sel _ _ _ _ _).1 x.2
    refine ⟨⟨?_, fun s i => lftV_mem c n _ i, fun s _ t _ => ?_⟩, fun a ha => ?_, fun q hq hlq => ?_, ?_⟩
    · have h1 : Continuous fun s => (rep x).1 (toGS Ω (S : Set Pl) s) := (rep x).2.1.comp (continuous_toGS Ω _)
      have h2 : Continuous fun s => lftV c n (E.symm ((rep x).1 (toGS Ω (S : Set Pl) s))) :=
        (continuous_of_discreteTopology (f := fun φ => lftV c n (E.symm φ))).comp h1
      exact h2.continuousOn
    · intro i
      dsimp only
      have hb : ∀ i, (lftV c n (Y x s) + mat (dual1 W) s *ᵥ lftV c n (Y x t)) i ∈ c.O := fun i =>
        add_mem (lftV_mem c n _ i) (CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i)
      refine cg_of_red (lftV_mem c n _ i) (hb i) ?_
      have e1 : (⟨(lftV c n (Y x s) + mat (dual1 W) s *ᵥ lftV c n (Y x t)) i, hb i⟩ : c.O) =
          ⟨lftV c n (Y x s) i, lftV_mem c n _ i⟩ +
            ⟨(mat (dual1 W) s *ᵥ lftV c n (Y x t)) i, CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i⟩ := rfl
      rw [e1, map_add (f := _), red_lftV, red_mulVec c n _ (hint' s) _ (lftV_mem c n _), red_lftV, hYc]
      simp only [red_lftV, Pi.add_apply]
      rfl
    · intro i
      have h1 : toGS Ω (S : Set Pl) a = 1 := MonoidHom.mem_ker.1 ha
      have h0 : (rep x).1 1 = 0 := by
        have := (rep x).2.2 1 1
        rw [mul_one, map_one, Module.End.one_apply] at this
        exact add_left_cancel (this.symm.trans (add_zero _).symm)
      show Cg n (lftV c n (Y x a) i) 0
      refine cg_of_red (lftV_mem c n _ i) (zero_mem _) ?_
      rw [red_lftV]
      simp only [Y, h1, h0, map_zero, Pi.zero_apply]
      exact (map_zero (red c n)).symm
    · obtain ⟨v0, hA0, hl0⟩ := hW.atL
      have hnot : ¬ IsPlaceOver A q := fun h => hlq ((eq_of_isPlaceOver hA0 h) ▸ hl0)
      have hBq : IsPlaceOver (Av A S ⟨q, hq⟩) q := isPlaceOver_Av A S ⟨q, hq⟩
      have hsel := hsel0 ⟨q, hq⟩
      have hLc : Lc c n W hint S hN A ⟨q, hq⟩ = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) ⟨q, hq⟩))
          ((Ine (F := ℚ) (Av A S ⟨q, hq⟩)).subgroupOf (Dec (F := ℚ) (Av A S ⟨q, hq⟩))) := if_neg hnot
      rw [mem_perpCond, hLc, ← hrep x] at hsel
      obtain ⟨m, hm⟩ := GlobalTheory.T.dualCocycle_coboundary_on_inertia_of_orthogonal hL l Ω n hn S (Mn c n) rho hcA μ hμ (Av A S ⟨q, hq⟩) q hBq hlq
        (restrictCocycles1 _ (locFam S (Av A S) ⟨q, hq⟩) (continuous_locFam S (Av A S) ⟨q, hq⟩) (rep x)) hsel
      refine ⟨Av A S ⟨q, hq⟩, hBq, lftV c n (E.symm m), lftV_mem c n _, fun s hs i => ?_⟩
      have hsD : s ∈ Dec (F := ℚ) (Av A S ⟨q, hq⟩) := hs.1
      have hms : (rep x).1 (toGS Ω (S : Set Pl) s) = twDual μ rho (toGS Ω (S : Set Pl) s) m - m := hm ⟨s, hsD⟩ hs
      have hb : (mat (dual1 W) s *ᵥ lftV c n (E.symm m) - lftV c n (E.symm m)) i ∈ c.O :=
        sub_mem (CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i) (lftV_mem c n _ i)
      refine cg_of_red (lftV_mem c n _ i) hb ?_
      have e1 : (⟨(mat (dual1 W) s *ᵥ lftV c n (E.symm m) - lftV c n (E.symm m)) i, hb⟩ : c.O) =
          ⟨(mat (dual1 W) s *ᵥ lftV c n (E.symm m)) i, CupCob.mulVec_mem c _ _ (hint' s) (lftV_mem c n _) i⟩ -
            ⟨lftV c n (E.symm m) i, lftV_mem c n _ i⟩ := rfl
      rw [e1, map_sub, red_mulVec c n _ (hint' s) _ (lftV_mem c n _), red_lftV, red_lftV]
      simp only [red_lftV, Y, hms, map_sub, hΨeq, Pi.sub_apply]
      rfl
    · obtain ⟨v0, hA0, hl0⟩ := hW.atL
      have hv0 : v0 ∈ S := hW.above v0 hl0
      have hAv : Av A S ⟨v0, hv0⟩ = A := if_pos hA0
      have hsel := hsel0 ⟨v0, hv0⟩
      have hLc : Lc c n W hint S hN A ⟨v0, hv0⟩ = ordCond c n W hint S hN (Av A S ⟨v0, hv0⟩) := if_pos hA0
      rw [mem_perpCond, hLc, ← hrep x] at hsel
      have hup : ∀ s ∈ Dec (F := ℚ) (Av A S ⟨v0, hv0⟩), mat W s 1 0 = 0 := by
        rw [hAv]; exact hW.upper
      obtain ⟨m, hm⟩ := ord_perp hL l Ω c n hn W hint hdet hW.cont S hN μ hμ (Av A S ⟨v0, hv0⟩) v0
        (isPlaceOver_Av A S ⟨v0, hv0⟩) hup (restrictCocycles1 _ _ (continuous_locFam S (Av A S) ⟨v0, hv0⟩) (rep x)) hsel
        (Y x) (fun s hs => hY x s)
      rw [hAv] at hm
      refine ⟨lft c n m, (lft c n m).2, fun s hs => ?_⟩
      refine cg_of_red (lftV_mem c n _ 1) (sub_mem (mul_mem (hint' s 1 1) (lft c n m).2) (lft c n m).2) ?_
      rw [red_lftV, hm s hs]
      show _ = red c n (⟨mat (dual1 W) s 1 1, hint' s 1 1⟩ * lft c n m - lft c n m)
      rw [map_sub, map_mul, red_lft]
      rfl
  · apply hne
    obtain ⟨v, hv, hcv⟩ := hcob
    apply Subtype.ext
    rw [← hrep x, ← hrep x', ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    refine (mem_coboundaries1 _ _).2 ⟨Phi c n (fun i => red c n ⟨v i, hv i⟩), fun g => ?_⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    have hs : ∀ i, Cg n (lftV c n (Y x s) i - lftV c n (Y x' s) i) ((mat (dual1 W) s *ᵥ v - v) i) :=
      hcv s (Subgroup.mem_top s)
    have key : Y x s - Y x' s = matQ c n (dual1 W) hint' s *ᵥ (fun i => red c n ⟨v i, hv i⟩) -
        (fun i => red c n ⟨v i, hv i⟩) := by
      funext i
      have h := red_of_cg (sub_mem (lftV_mem c n (Y x s) i) (lftV_mem c n (Y x' s) i))
        (sub_mem (CupCob.mulVec_mem c _ _ (hint' s) hv i) (hv i)) (hs i)
      rw [show (⟨lftV c n (Y x s) i - lftV c n (Y x' s) i, sub_mem (lftV_mem c n (Y x s) i) (lftV_mem c n (Y x' s) i)⟩ : c.O) =
          ⟨lftV c n (Y x s) i, lftV_mem c n _ i⟩ - ⟨lftV c n (Y x' s) i, lftV_mem c n _ i⟩ from rfl,
        show (⟨(mat (dual1 W) s *ᵥ v) i - v i, sub_mem (CupCob.mulVec_mem c _ _ (hint' s) hv i) (hv i)⟩ : c.O) =
          ⟨(mat (dual1 W) s *ᵥ v) i, CupCob.mulVec_mem c _ _ (hint' s) hv i⟩ - ⟨v i, hv i⟩ from rfl,
        map_sub, map_sub, red_lftV, red_lftV, red_mulVec c n _ (hint' s) _ hv] at h
      rw [Pi.sub_apply, Pi.sub_apply, h]
      rfl
    have h2 := congrArg (Phi c n) key
    rw [map_sub, map_sub, hY x s, hY x' s, heq s] at h2
    exact h2

end GlobalTheory.Ord2.SelPerp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochainsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ, μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∃ z : SelD c n W hint S hN A hW.cont μ → (G ℚ Ω → Fin 2 → Qbar l), (∀ x, GwCount.SelN c n S A (dual1 W) (z x)) ∧ ∀ x x', x ≠ x' → ¬ Cob1 c n (dual1 W) ⊤ (z x - z x') := by
  first | exact @GlobalTheory.Ord2.SelPerp.sel_perp | exact GlobalTheory.Ord2.SelPerp.sel_perp | (intros; apply GlobalTheory.Ord2.SelPerp.sel_perp <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.ord_perp | exact GlobalTheory.Ord2.SelPerp.ord_perp | (intros; apply GlobalTheory.Ord2.SelPerp.ord_perp <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.phi_bijective | exact GlobalTheory.Ord2.SelPerp.phi_bijective | (intros; apply GlobalTheory.Ord2.SelPerp.phi_bijective <;> assumption)
end
end
