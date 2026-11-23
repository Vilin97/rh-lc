module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LowLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MsetSep
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LowStab

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.lowStab :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V), IsMultiGl F → ∀ (ν : ι → Fin n → ℂ) (v : V), (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
      v ∈ low F v ∧ Stab F (low F v) := by
  intro ι V _ _ _ n F hF ν v hv
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have hvlow : v ∈ low F v := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    rw [Submodule.mem_sInf]
    intro p hp
    exact hp.1
  have hlow : ∀ t (i j : Fin n), j < i → ∀ w ∈ low F v, F t i j w ∈ low F v := by
    intro t i j hji w hw
    unfold UpperTheory.V.AlgRepEndIrreducible.low at hw ⊢
    rw [Submodule.mem_sInf] at hw ⊢
    intro p hp
    exact hp.2 t i j hji w (hw p hp)
  let W' : Submodule ℂ V := low F v ⊓ ⨅ t, ⨅ i, ⨅ j, (low F v).comap (F t i j)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ low F v ∧ ∀ t i j, F t i j w ∈ low F v := by
    intro w
    simp [W', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  have hvW : v ∈ W' := by
    rw [hmem]
    refine ⟨hvlow, fun t i j => ?_⟩
    rcases lt_trichotomy i j with h | h | h
    · rw [(hv t).2 i j h]
      exact zero_mem _
    · subst h
      rw [(hv t).1 i]
      exact Submodule.smul_mem _ _ hvlow
    · exact hlow t i j h v hvlow
  have hWst : ∀ t (k l : Fin n), l < k → ∀ w ∈ W', F t k l w ∈ W' := by
    intro t k l hlk w hw
    rw [hmem] at hw ⊢
    refine ⟨hlow t k l hlk w hw.1, fun s i j => ?_⟩
    by_cases hst : s = t
    · subst hst
      have h1 := congrArg (fun f : Module.End ℂ V => f w) (hgl s i j k l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      refine add_mem (sub_mem ?_ ?_) (hlow s k l hlk _ (hw.2 s i j))
      · split_ifs
        · exact hw.2 s i l
        · rw [LinearMap.zero_apply]
          exact zero_mem _
      · split_ifs
        · exact hw.2 s k j
        · rw [LinearMap.zero_apply]
          exact zero_mem _
    · have h1 := congrArg (fun f : Module.End ℂ V => f w) (hcomm s t hst i j k l)
      simp only [Module.End.mul_apply] at h1
      rw [h1]
      exact hlow t k l hlk _ (hw.2 s i j)
  have hle : low F v ≤ W' := by
    unfold UpperTheory.V.AlgRepEndIrreducible.low
    exact sInf_le ⟨hvW, hWst⟩
  exact ⟨hvlow, fun t i j w hw => ((hmem w).mp (hle hw)).2 t i j⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HwIso

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.hwIso :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (F' : ι → Fin n → Fin n → Module.End ℂ V'),
      IsMultiGl F → IsMultiGl F' → (∀ W, Stab F W → W = ⊥ ∨ W = ⊤) → (∀ W, Stab F' W → W = ⊥ ∨ W = ⊤) →
      ∀ (ν : ι → Fin n → ℂ) (v : V) (v' : V'), v ≠ 0 → v' ≠ 0 → (∀ t, Formalism.REAL.IsHW (F t) (ν t) v) →
        (∀ t, Formalism.REAL.IsHW (F' t) (ν t) v') → ∃ T : V ≃ₗ[ℂ] V', ∀ t i j x, T (F t i j x) = F' t i j (T x) := by
  intro ι V _ _ _ n F V' _ _ F' hF hF' hS hS' ν v v' hv0 hv0' hv hv'
  let P : ι → Fin n → Fin n → Module.End ℂ (V × V') := fun t i j => (F t i j).prodMap (F' t i j)
  have hPa : ∀ t i j (x : V) (y : V'), P t i j (x, y) = (F t i j x, F' t i j y) := fun _ _ _ _ _ => rfl
  have hP : IsMultiGl P := by
    refine ⟨fun t i j k l => ?_, fun s t hst i j k l => ?_⟩
    · refine LinearMap.ext fun z => ?_
      have e := LinearMap.congr_fun (hF.1 t i j k l) z.1
      have e' := LinearMap.congr_fun (hF'.1 t i j k l) z.2
      refine Prod.ext (e.trans ?_) (e'.trans ?_)
      · split_ifs <;> rfl
      · split_ifs <;> rfl
    · refine LinearMap.ext fun z => ?_
      exact Prod.ext (LinearMap.congr_fun (hF.2 s t hst i j k l) z.1)
        (LinearMap.congr_fun (hF'.2 s t hst i j k l) z.2)
  have hvv : ∀ t, Formalism.REAL.IsHW (P t) (ν t) (v, v') := fun t =>
    ⟨fun i => Prod.ext ((hv t).1 i) ((hv' t).1 i),
      fun i j h => Prod.ext ((hv t).2 i j h) ((hv' t).2 i j h)⟩
  obtain ⟨hm, hst⟩ := lowStab ι (V × V') n P hP ν (v, v') hvv
  have hl := lowLine ι (V × V') n P hP ν (v, v') hvv
  generalize low P (v, v') = W at hm hst hl
  have hA : ∀ y : V', ((0 : V), y) ∈ W → y = 0 := by
    rcases hS' (W.comap (LinearMap.inr ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inr_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : ((0 : V), v') ∈ W := (Submodule.eq_top_iff'.1 h v' :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv' t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.fst hc).symm).resolve_right hv0
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.snd hc) hv0'
  have hB : ∀ x : V, (x, (0 : V')) ∈ W → x = 0 := by
    rcases hS (W.comap (LinearMap.inl ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw
      rwa [LinearMap.inl_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : (v, (0 : V')) ∈ W := (Submodule.eq_top_iff'.1 h v :)
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by
        rw [hPa, map_zero, (hv t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.snd hc).symm).resolve_right hv0'
      rw [h2, zero_smul] at hc
      exact absurd (congrArg Prod.fst hc) hv0
  have hC : W.map (LinearMap.fst ℂ V V') = ⊤ := by
    refine (hS _ ?_).resolve_left fun h => hv0 ((Submodule.eq_bot_iff _).1 h v ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have hD : W.map (LinearMap.snd ℂ V V') = ⊤ := by
    refine (hS' _ ?_).resolve_left fun h => hv0' ((Submodule.eq_bot_iff _).1 h v' ⟨_, hm, rfl⟩)
    rintro t i j _ ⟨z, hz, rfl⟩
    exact ⟨_, hst t i j z hz, rfl⟩
  have b1 : Function.Bijective ((LinearMap.fst ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : x = 0)
      exact Subtype.ext (Prod.ext rfl (hA y hz))
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hC x
      exact ⟨⟨z, hz⟩, rfl⟩
  have b2 : Function.Bijective ((LinearMap.snd ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : y = 0)
      exact Subtype.ext (Prod.ext (hB x hz) rfl)
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hD x
      exact ⟨⟨z, hz⟩, rfl⟩
  have key : ∀ z : W, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) z.1.1 = z.1.2 := by
    intro z
    have : (LinearEquiv.ofBijective _ b1).symm z.1.1 = z := (LinearEquiv.ofBijective _ b1).symm_apply_apply z
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨(LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2), fun t i j x => ?_⟩
  obtain ⟨z, rfl⟩ := b1.2 x
  exact (key ⟨_, hst t i j z.1 z.2⟩).trans (congrArg (F' t i j) (key z).symm)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.MultiHW

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.multiHW :
    ∀ (ι V : Type) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ) (F : ι → Fin n → Fin n → Module.End ℂ V) [FiniteDimensional ℂ V] [Nontrivial V], IsMultiGl F →
      ∃ (ν : ι → Fin n → ℂ) (v : V), v ≠ 0 ∧ ∀ t, Formalism.REAL.IsHW (F t) (ν t) v ∧ Dom (ν t) := by
  intro ι V _ _ _ n F _ _ hM
  obtain ⟨hF, hcomm⟩ := hM
  classical
  have hc : ∀ t k i j, F t k k * F t i j - F t i j * F t k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F t i j := by
    intro t k i j
    rw [hF t]
    by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let G : ι → Module.End ℂ V := fun s => ∑ k : Fin n, ((k : ℕ) : ℂ) • F s k k
  have hG : ∀ t i j, G t * F t i j - F t i j * G t = (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hG' : ∀ s t, s ≠ t → ∀ i j, G s * F t i j - F t i j * G s = 0 := by
    intro s t hst i j
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, hcomm s t hst, sub_self]
  let H : Module.End ℂ V := ∑ s, G s
  have hH : ∀ t i j, H * F t i j = F t i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := by
    intro t i j
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single t (fun s _ hs => hG' s t hs i j) (by simp), hG]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re (Module.End.finite_hasEigenvalue H)
    (Module.End.exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector (fun p : ι × Fin n => F p.1 p.2 p.2)
    (fun p q => by
      obtain ⟨s, i⟩ := p
      obtain ⟨t, j⟩ := q
      by_cases hst : s = t
      · subst hst
        rw [← sub_eq_zero, hc]
        by_cases h : i = j <;> simp [h, eq_comm]
      · exact hcomm s t hst _ _ _ _) (H.eigenspace l) hl
    (fun k v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, hH]
      simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ t i j, i < j → F t i j v = 0 := by
    intro t i j hij
    by_contra h0
    have h1 : H (F t i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F t i j v := by
      rw [← Module.End.mul_apply, hH]
      simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2
    exact absurd hij (not_lt.2 h2)
  have hν' : ∀ t k, F t k k v = ν (t, k) • v := fun t k => hν (t, k)
  refine ⟨fun t k => ν (t, k), v, hv0, fun t => ⟨⟨hν' t, hup t⟩, fun i j hij =>
    GlobalTheory.AlgInfChar.exists_nat_of_primitive (F t i j) (F t j i) (F t i i - F t j j) ?_ ?_ v _ hv0
      (hup t i j hij) ?_⟩⟩
  · rw [hF t]; simp
  · have h1 := hc t i j i
    have h2 := hc t j j i
    simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]
    linear_combination (norm := module) h1 - h2
  · simp [hν', sub_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.WtEq

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.wtEq :
    ∀ (n : ℕ) (ν ν' : Fin n → ℂ), Dom ν → Dom ν' →
      (∀ u : ℂ, ∏ k : Fin n, (u - (k : ℂ) + ν k) = ∏ k : Fin n, (u - (k : ℂ) + ν' k)) → ν = ν' := by
  intro n ν ν' hν hν' hp
  classical
  have key : ∀ μ : Fin n → ℂ, Dom μ → ∀ i : Fin n,
      (Multiset.filter (fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1)
        (Multiset.map (fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val)).card = (i : ℕ) := by
    intro μ hμ i
    have hP : ∀ j : Fin n, (∃ k : ℕ, μ j - (j : ℂ) - (μ i - (i : ℂ)) = (k : ℂ) + 1) ↔ j < i := by
      intro j
      constructor
      · rintro ⟨k, hk⟩
        by_contra hji
        rcases (not_lt.1 hji).lt_or_eq with hij | hij
        · obtain ⟨m, hm⟩ := hμ i j hij
          have h1 : (((i : ℕ) : ℕ) : ℂ) = ((k + 1 + m + (j : ℕ) : ℕ) : ℂ) := by
            push_cast
            linear_combination hk + hm
          have h2 : (i : ℕ) = k + 1 + m + (j : ℕ) := Nat.cast_injective h1
          have h3 : (i : ℕ) < (j : ℕ) := hij
          omega
        · subst hij
          have h1 : ((k + 1 : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by
            push_cast
            linear_combination -hk
          have h2 : k + 1 = 0 := Nat.cast_injective h1
          omega
      · intro hji
        obtain ⟨m, hm⟩ := hμ j i hji
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
        have hi : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) + (d : ℂ) + 1 := by
          exact_mod_cast hd
        refine ⟨m + d, ?_⟩
        push_cast
        linear_combination hm + hi
    rw [Multiset.filter_map, Multiset.card_map]
    have hf : Multiset.filter ((fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) ∘
        fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val
          = Multiset.filter (fun j : Fin n => j < i) Finset.univ.val :=
      Multiset.filter_congr (fun j _ => hP j)
    rw [hf]
    calc (Multiset.filter (fun j : Fin n => j < i) Finset.univ.val).card
        = (Finset.univ.filter (fun j : Fin n => j < i)).card := rfl
      _ = (Finset.Iio i).card := by
        congr 1
        ext j
        simp
      _ = (i : ℕ) := Fin.card_Iio i
  have hm : Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val
      = Multiset.map (fun j : Fin n => ν' j - (j : ℂ)) Finset.univ.val := by
    apply msetSep
    intro u
    rw [Multiset.map_map, Multiset.map_map]
    have e : ∀ μ : Fin n → ℂ, (Multiset.map ((fun x => u + x) ∘ fun j : Fin n => μ j - (j : ℂ))
        Finset.univ.val).prod = ∏ k : Fin n, (u - (k : ℂ) + μ k) := by
      intro μ
      rw [Finset.prod_eq_multiset_prod]
      congr 2
      funext k
      dsimp
      ring
    rw [e, e]
    exact hp u
  funext i
  have hmem : ν' i - (i : ℂ) ∈ Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val := by
    rw [hm]
    exact Multiset.mem_map.2 ⟨i, by simp, rfl⟩
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
  have h1 := key ν hν j
  have h2 := key ν' hν' i
  rw [← hm, ← hj, h1] at h2
  have hji : j = i := Fin.ext h2
  subst hji
  linear_combination hj
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIsoLie

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem hw_prod {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ)
    (h : UpperTheory.V.Af.AlgInfChar Ξ τ m) (hgl : Formalism.REAL.GlRel (eEnd Ξ τ)) (ν : Fin a → ℂ) (v : Fin Ξ.d → ℂ)
    (hv : v ≠ 0) (hw : Formalism.REAL.IsHW (eEnd Ξ τ) ν v) (u : ℂ) :
    ∏ k : Fin a, (u - (k : ℂ) + ν k) = (m.map (u - ((a : ℂ) - 1) / 2 + ·)).prod := by
  let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
  have hf : ∀ M v, f M v = M *ᵥ v := fun _ _ => rfl
  have h1 := Formalism.REAL.qDetHW _ a (fun i j => f (eL Ξ.dmat τ i j)) ν v hgl hw u
  have h2 : Formalism.REAL.qdet (eL Ξ.dmat τ) u =
      (m.map (u - ((a : ℂ) - 1) / 2 + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
    have h3 := h.2 (u - ((a : ℂ) - 1) / 2)
    rw [sub_add_cancel] at h3
    exact h3
  rw [← map_qdet, h2, hf, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  exact (smul_left_injective ℂ hv h1).symm

theorem UpperTheory.V.AlgRepEndIrreducible.algIsoLie :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a) (m : (E →+* ℂ) → Multiset ℂ),
      (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ τ (m τ)) → (∀ τ, UpperTheory.V.Af.AlgInfChar Ξ' τ (m τ)) →
      ∃ T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ), ∀ τ i j v, T (eEnd Ξ τ i j v) = eEnd Ξ' τ i j (T v) := by
  intro E _ _ _ a Ξ Ξ' m h h'
  haveI : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  haveI : Nonempty (Fin Ξ'.d) := ⟨⟨0, Ξ'.pos⟩⟩
  obtain ⟨hM, hS⟩ := algIrr E a Ξ
  obtain ⟨hM', hS'⟩ := algIrr E a Ξ'
  obtain ⟨ν, v, hv, hν⟩ := multiHW _ _ a (eEnd Ξ) hM
  obtain ⟨ν', v', hv', hν'⟩ := multiHW _ _ a (eEnd Ξ') hM'
  obtain rfl : ν = ν' := funext fun τ => wtEq a _ _ (hν τ).2 (hν' τ).2 fun u =>
    (hw_prod Ξ τ _ (h τ) (hM.1 τ) _ v hv (hν τ).1 u).trans
      (hw_prod Ξ' τ _ (h' τ) (hM'.1 τ) _ v' hv' (hν' τ).1 u).symm
  exact hwIso _ _ a (eEnd Ξ) _ (eEnd Ξ') hM hM' hS hS' ν v v' hv hv' (fun τ => (hν τ).1) (fun τ => (hν' τ).1)
end
end
