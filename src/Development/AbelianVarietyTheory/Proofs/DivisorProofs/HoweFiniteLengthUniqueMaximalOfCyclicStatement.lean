module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Formalism.LocalRingCardinality.DataTheta
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLeStatement
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquot
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainLengthLeFinrankAddOne

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem chain_length_le_finrank_add_one : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (G U C : Submodule ℂ V), FiniteDimensional ℂ U → G ≤ U ⊔ C → ∀ (m : ℕ) (N : Fin m → Submodule ℂ V), StrictMono N → (∀ k, C ≤ N k) → (∀ k l, k < l → ∃ v ∈ N l, v ∈ G ∧ v ∉ N k) → m ≤ Module.finrank ℂ U + 1 := by
  intro V _ _ G U C hU hGUC m N hN hC hsep
  let g : Fin m → Submodule ℂ U := fun k => (N k).comap U.subtype
  have hg : StrictMono g := by
    intro k l hkl
    refine lt_of_le_of_ne (fun x hx => hN.monotone hkl.le hx) ?_
    intro heq
    obtain ⟨v, hvl, hvG, hvk⟩ := hsep k l hkl
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.mp (hGUC hvG)
    have hcl : c ∈ N l := hC l hc
    have hul : u ∈ N l := by simpa using (N l).sub_mem hvl hcl
    have hmem : (⟨u, hu⟩ : U) ∈ g l := hul
    rw [← heq] at hmem
    exact hvk ((N k).add_mem hmem (hC k hc))
  let f : Fin m → Fin (Module.finrank ℂ U + 1) := fun k =>
    ⟨Module.finrank ℂ (g k), Nat.lt_succ_of_le (Submodule.finrank_le _)⟩
  have hf : Function.Injective f := by
    intro k l h
    have h' : Module.finrank ℂ (g k) = Module.finrank ℂ (g l) := congrArg Fin.val h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'
    · exact (ne_of_lt (Submodule.finrank_lt_finrank_of_lt (hg hlt))) h'.symm
  simpa using Fintype.card_le_of_injective f hf

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HwSubStableOfComm

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem hwSub_stable_of_comm {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (f : Module.End ℂ V)
    (hf : ∀ Z v, f (act Z v) = act Z (f v)) (μ : Ix p q → ℚ) :
    ∀ v ∈ hwSub act μ, f v ∈ hwSub act μ := by
  intro v hv
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
  obtain ⟨h1, h2⟩ := hv
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · have := congrArg f (h1 a)
    simpa [hf, map_sub, map_smul] using this
  · rw [← hf, h2 a b hab, map_zero]

theorem hw_joint_split : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) →
    ∀ N N' : Submodule ℂ V, (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') →
    ∀ μ : ∀ w, Ix (R w) (S w) → ℚ,
    (N ⊔ N') ⊓ (⨅ w, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w, hwSub (a w) (μ w)) := by
  intro T _ _ R S V _ _ a hg hc N N' hN hN' μ
  have key : ∀ s : Finset T, (N ⊔ N') ⊓ (⨅ w ∈ s, hwSub (a w) (μ w)) ≤
      (N ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) ⊔ (N' ⊓ ⨅ w ∈ s, hwSub (a w) (μ w)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih =>
      set H := ⨅ w ∈ s, hwSub (a w) (μ w) with hH
      have hHst : ∀ X, ∀ v ∈ H, a w X v ∈ H := by
        intro X v hv
        rw [hH, Submodule.mem_iInf] at hv ⊢
        intro w'
        have hv' := hv w'
        rw [Submodule.mem_iInf] at hv' ⊢
        intro hw'
        have hne : w ≠ w' := fun h => hws (h ▸ hw')
        exact hwSub_stable_of_comm (a w') (a w X) (fun Z u => hc w w' hne X Z u) (μ w') v (hv' hw')
      have hK : ∀ M : Submodule ℂ V, (∀ Z, ∀ y ∈ M, a w Z y ∈ M) → KStable (a w) (M ⊓ H) := by
        intro M hM X _ v hv
        exact Submodule.mem_inf.mpr ⟨hM X v (Submodule.mem_inf.mp hv).1, hHst X v (Submodule.mem_inf.mp hv).2⟩
      have hsp := GlobalTheory.T.howeHighestWeight_sup_stable_le (R w) (S w) V (a w) (hg w) (N ⊓ H) (N' ⊓ H) (hK N (hN w)) (hK N' (hN' w)) (μ w)
      rw [Finset.iInf_insert]
      calc (N ⊔ N') ⊓ (hwSub (a w) (μ w) ⊓ H) = ((N ⊔ N') ⊓ H) ⊓ hwSub (a w) (μ w) := by
              rw [inf_comm (hwSub (a w) (μ w)) H, inf_assoc]
        _ ≤ ((N ⊓ H) ⊔ (N' ⊓ H)) ⊓ hwSub (a w) (μ w) := inf_le_inf_right _ ih
        _ ≤ ((N ⊓ H) ⊓ hwSub (a w) (μ w)) ⊔ ((N' ⊓ H) ⊓ hwSub (a w) (μ w)) := hsp
        _ = (N ⊓ (hwSub (a w) (μ w) ⊓ H)) ⊔ (N' ⊓ (hwSub (a w) (μ w) ⊓ H)) := by
              rw [inf_assoc, inf_assoc, inf_comm H]
  simpa using key Finset.univ

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedHighestWeightVectorQuadraticSubquotStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient : ∀ (p q : ℕ) (α β α' β' : ℂ), ∃ B : ℚ, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, N < N' → Stab act N → Stab act N' → QuadMod act α β α' β' N N' → ∃ μ : Ix p q → ℚ, (∀ a, |μ a| ≤ B) ∧ ∃ v ∈ N', v ∈ hwSub act μ ∧ v ∉ N := by
  first | exact @GlobalTheory.HoweR.exists_hwSub_of_quadMod | exact GlobalTheory.HoweR.exists_hwSub_of_quadMod | (intros; apply GlobalTheory.HoweR.exists_hwSub_of_quadMod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiPlaceStep

section

@[expose] public section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR.Places

section One

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_hwSub_iff (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub a μ ↔ (∀ c, a (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → a (Eab c d) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem hw_comm {a : Mat p q →ₗ[ℂ] Module.End ℂ V} {L : Module.End ℂ V} (h : ∀ Z v, L (a Z v) = a Z (L v))
    {μ : Ix p q → ℚ} {v : V} (hv : v ∈ hwSub a μ) : L v ∈ hwSub a μ := by
  rw [mem_hwSub_iff] at hv ⊢
  refine ⟨fun c => ?_, fun c d hcd => ?_⟩
  · rw [← h, hv.1 c, map_smul]
  · rw [← h, hv.2 c d hcd, map_zero]

end One

section Quad

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem qop_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) (α β : ℂ)
    (a b : ι) {v : M} (hv : v ∈ H) : qop F α β a b v ∈ H := by
  unfold qop
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply]
  refine H.sub_mem (H.sub_mem (H.sum_mem fun c _ => hF _ _ _ (hF _ _ _ hv)) (H.smul_mem _ (hF _ _ _ hv))) ?_
  by_cases hab : a = b
  · simpa [hab] using H.smul_mem β hv
  · simp [hab]

theorem negT_mem (F : ι → ι → Module.End ℂ M) (H : Submodule ℂ M) (hF : ∀ a b, ∀ u ∈ H, F a b u ∈ H) :
    ∀ a b, ∀ u ∈ H, negT F a b u ∈ H := fun a b u hu => by
  simp only [negT, LinearMap.neg_apply]
  exact H.neg_mem (hF b a u hu)

end Quad

theorem multi_place_step : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (α β α' β' : T → ℂ), ∃ B : ℚ,
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) →
    (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ N N' : Submodule ℂ V, N < N' →
    (∀ w, Stab (a w) N) → (∀ w, Stab (a w) N') → (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) N N') →
    ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) ∧ ∃ v ∈ N', (∀ w, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
  intro T _ _ R S α β α' β'
  have hk := fun w => GlobalTheory.T.exists_boundedHighestWeightVector_quadraticSubquotient (R w) (S w) (α w) (β w) (α' w) (β' w)
  choose Bw hBw using hk
  refine ⟨∑ w, |Bw w|, ?_⟩
  intro V _ _ a hG hc N N' hNN' hsN hsN' hQ
  have hB : ∀ w, |Bw w| ≤ ∑ w, |Bw w| := fun w =>
    Finset.single_le_sum (f := fun w => |Bw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)
  have h0 : (0 : ℚ) ≤ ∑ w, |Bw w| := Finset.sum_nonneg fun w _ => abs_nonneg (Bw w)
  have key : ∀ s : Finset T, ∃ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ ∑ w, |Bw w|) ∧
      ∃ v ∈ N', (∀ w ∈ s, v ∈ hwSub (a w) (μ w)) ∧ v ∉ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨v, hv, hvN⟩ := SetLike.exists_of_lt hNN'
      exact ⟨fun _ _ => 0, fun _ _ => by simpa using h0, v, hv, by simp, hvN⟩
    | insert w s hws ih =>
      obtain ⟨μ, hμB, v, hvN', hvs, hvN⟩ := ih
      let H : Submodule ℂ V := ⨅ w' ∈ s, hwSub (a w') (μ w')
      have memH : ∀ u, u ∈ H ↔ ∀ w' ∈ s, u ∈ hwSub (a w') (μ w') := fun u => by
        simp only [H, Submodule.mem_iInf]
      have sH : ∀ Z, ∀ u ∈ H, a w Z u ∈ H := fun Z u hu => by
        rw [memH] at hu ⊢
        intro w' hw'
        exact hw_comm (fun Z' x => hc w w' (fun e => hws (e ▸ hw')) Z Z' x) (hu w' hw')
      have sU : ∀ c d, ∀ u ∈ H, units (a w) c d u ∈ H := fun c d u hu => sH _ u hu
      have hlt : N ⊓ H < N' ⊓ H := by
        refine lt_of_le_of_ne (inf_le_inf_right _ hNN'.le) fun e => hvN ?_
        have : v ∈ N' ⊓ H := ⟨hvN', (memH v).2 hvs⟩
        rw [← e] at this
        exact this.1
      have hS1 : Stab (a w) (N ⊓ H) := fun Z u hu => ⟨hsN w Z u hu.1, sH Z u hu.2⟩
      have hS2 : Stab (a w) (N' ⊓ H) := fun Z u hu => ⟨hsN' w Z u hu.1, sH Z u hu.2⟩
      have hQ' : QuadMod (a w) (α w) (β w) (α' w) (β' w) (N ⊓ H) (N' ⊓ H) := fun c d u hu =>
        ⟨⟨(hQ w c d u hu.1).1, qop_mem _ H sU _ _ c d hu.2⟩,
          ⟨(hQ w c d u hu.1).2, qop_mem _ H (negT_mem _ H sU) _ _ c d hu.2⟩⟩
      obtain ⟨ν, hνB, u, huN', huhw, huN⟩ := hBw w V (a w) (hG w) _ _ hlt hS1 hS2 hQ'
      refine ⟨Function.update μ w ν, fun w' c => ?_, u, huN'.1, fun w' hw' => ?_, fun h => huN ⟨h, huN'.2⟩⟩
      · rcases eq_or_ne w' w with rfl | e
        · simp only [Function.update_self]
          exact (hνB c).trans ((le_abs_self _).trans (hB w'))
        · rw [Function.update_of_ne e]
          exact hμB w' c
      · rcases Finset.mem_insert.1 hw' with rfl | hw''
        · simpa using huhw
        · have hne : w' ≠ w := fun e => hws (e ▸ hw'')
          rw [Function.update_of_ne hne]
          exact (memH u).1 huN'.2 w' hw''
  obtain ⟨μ, hμ, v, hv, hvs, hvN⟩ := key Finset.univ
  exact ⟨μ, hμ, v, hv, fun w => hvs w (Finset.mem_univ w), hvN⟩

end GlobalTheory.HoweR.Places

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclic

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem howe_finiteLength_uniqueMaximal_of_cyclic : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  intro T _ _ R S V _ _ a hG hc C α β α' β' hQ hAdm hCyc
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB⟩ := Places.multi_place_step T R S α β α' β'
    obtain ⟨U, hU, hUC⟩ := hAdm B
    let G : Submodule ℂ V := ⨆ (μ : ∀ w, Ix (R w) (S w) → ℚ) (_ : ∀ w c, |μ w c| ≤ B), ⨅ w, hwSub (a w) (μ w)
    have hGUC : G ≤ U ⊔ C := iSup_le fun μ => iSup_le fun h => hUC μ h
    refine ⟨Module.finrank ℂ U + 1, fun m N hN hNk => ?_⟩
    refine chain_length_le_finrank_add_one V G U C hU hGUC m N hN (fun k => (hNk k).2) ?_
    intro k l hkl
    have hQ' : ∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) (N k) (N l) := fun w c d u _ =>
      ⟨(hNk k).2 (hQ w c d u Submodule.mem_top).1, (hNk k).2 (hQ w c d u Submodule.mem_top).2⟩
    obtain ⟨μ, hμB, v, hvl, hvhw, hvk⟩ :=
      hB V a hG hc (N k) (N l) (hN hkl) (fun w => (hNk k).1 w) (fun w => (hNk l).1 w) hQ'
    refine ⟨v, hvl, ?_, hvk⟩
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    exact (le_iSup_of_le μ (le_iSup_of_le hμB le_rfl) : (⨅ w, hwSub (a w) (μ w)) ≤ G) hv
  · intro N N' hN hCN hNt hN' hCN' hN't hsup
    obtain ⟨μ, v, hvhw, hgen, hmult⟩ := hCyc
    have hv : v ∈ ⨅ w, hwSub (a w) (μ w) := Submodule.mem_iInf _ |>.mpr hvhw
    have hv2 : v ∈ (N ⊔ N') ⊓ ⨅ w, hwSub (a w) (μ w) := ⟨by rw [hsup]; exact Submodule.mem_top, hv⟩
    have hsp := hw_joint_split T R S V a hG hc N N' hN hN' μ hv2
    obtain ⟨n, hn, n', hn', hnn⟩ := Submodule.mem_sup.mp hsp
    obtain ⟨y, hy, c, hc', hyc⟩ := Submodule.mem_sup.mp (hmult hn.2)
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hy
    by_cases hx : x = 0
    · subst hx
      have hnC : n = c := by rw [← hyc]; simp
      have hvN' : v ∈ N' := by
        rw [← hnn]; exact N'.add_mem (hCN' (hnC ▸ hc')) hn'.1
      exact hN't (hgen N' hN' hCN' hvN')
    · have hvN : v ∈ N := by
        have h1 : x • v ∈ N := by
          have : x • v = n - c := by rw [← hyc]; simp
          rw [this]; exact N.sub_mem hn.1 (hCN hc')
        have := N.smul_mem x⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hx, one_smul] at this
      exact hNt (hgen N hN hCN hvN)

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclicStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.howeAlg_of_cyclic_highest_weight : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  first | exact @GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | exact GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | (intros; apply GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic <;> assumption)
end
end
