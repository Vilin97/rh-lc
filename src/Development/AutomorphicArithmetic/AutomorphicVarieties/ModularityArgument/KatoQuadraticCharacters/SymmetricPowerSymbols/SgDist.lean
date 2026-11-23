module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SgDistribution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplexStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAdmissibleSmoothingFactorDividedIndices

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : admitted c x) (hm : 0 < m) :
    admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simpa only [Finset.prod_apply, sgC] using
    GlobalTheory.SiegDist.sg_distribution c m x (UpperHalfPlane.ofComplex z) hA hm hcm

end GlobalTheory.KZDist
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SgDist

section

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem siegel_admissible_to_rat (c M : ℕ) (hc : 1 < c) (h6 : Nat.Coprime c 6) (hM : 0 < M) (hcM : Nat.Coprime c M)
    (x : Row M) (hx : x ≠ 0) : GlobalTheory.Sieg.admitted c (toQ M x) := by
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨hc, h6, ?_⟩
  rintro ⟨⟨n0, hn0⟩, ⟨n1, hn1⟩⟩
  apply hx
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ i : Fin 2, ∀ n : ℤ, (n : ℚ) = c * toQ M x i → x i = 0 := by
    intro i n hn
    have hlt := ZMod.val_lt (x i)
    have e : (n : ℚ) * M = (c * (x i).val : ℕ) := by
      rw [hn, toQ]
      push_cast
      field_simp
    have e' : n * (M : ℤ) = ((c * (x i).val : ℕ) : ℤ) := by exact_mod_cast e
    have hd : (M : ℤ) ∣ ((c * (x i).val : ℕ) : ℤ) := ⟨n, by rw [← e', mul_comm]⟩
    have hd' : M ∣ c * (x i).val := by exact_mod_cast hd
    have hv : M ∣ (x i).val := (Nat.Coprime.symm hcM).dvd_of_dvd_mul_left hd'
    have hv0 : (x i).val = 0 := by
      rcases Nat.eq_zero_or_pos (x i).val with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h hv) (not_le.mpr hlt)
    exact (ZMod.val_eq_zero _).mp hv0
  funext i
  fin_cases i
  · exact key 0 n0 hn0
  · exact key 1 n1 hn1

private theorem add_mul_lt_mul {k M a v : ℕ} (ha : a < k) (hv : v < M) : v + a * M < k * M := by
  have h1 : v + a * M < (a + 1) * M := by nlinarith
  have h2 : (a + 1) * M ≤ k * M := Nat.mul_le_mul_right _ ha
  omega

private theorem dn_val (k M : ℕ) [NeZero (k * M)] (x' : Row (k * M)) (i : Fin 2) :
    (dn k M x' i).val = (x' i).val % M := by
  show (ZMod.castHom _ (ZMod M) (x' i)).val = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

private theorem val_lt_mul_of_zmod_mul {k M : ℕ} (y : ZMod (k * M)) (hkM : k * M ≠ 0) : y.val < M * k := by
  haveI : NeZero (k * M) := ⟨hkM⟩
  have h := ZMod.val_lt y
  linarith [Nat.mul_comm k M]

theorem UpperTheory.V.Z.Kato.Sym.sgDist :
    UpperTheory.V.Z.Kato.Sym.SgDist := by
  classical
  intro Ω _ _ _ ε X c k M _ hc h6 hcop x hx
  have hkM : k * M ≠ 0 := NeZero.ne _
  have hk : 0 < k := Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))
  have hM : 0 < M := Nat.pos_of_ne_zero (fun h => hkM (by simp [h]))
  haveI : NeZero M := ⟨hM.ne'⟩
  have hcM : c.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M k) hcop
  have hck : c.Coprime k := Nat.Coprime.coprime_dvd_right (dvd_mul_right k M) hcop
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have split : ∀ x' : Row (k * M), dn k M x' = x → ∀ i : Fin 2,
      (x' i).val = (x i).val + (x' i).val / M * M := by
    intro x' hx' i
    have h := dn_val k M x' i
    rw [hx'] at h
    rw [h, Nat.mod_add_div']
  have qlt : ∀ x' : Row (k * M), ∀ i : Fin 2, (x' i).val / M < k := fun x' i =>
    Nat.div_lt_of_lt_mul (val_lt_mul_of_zmod_mul (x' i) hkM)
  let sel : ℕ × ℕ → Fin 2 → ℕ := fun p => ![p.1, p.2]
  let j : ℕ × ℕ → Row (k * M) := fun p i => (((x i).val + sel p i * M : ℕ) : ZMod (k * M))
  have jval : ∀ p ∈ Finset.range k ×ˢ Finset.range k, ∀ i : Fin 2,
      (j p i).val = (x i).val + sel p i * M := by
    intro p hp i
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    have hs : sel p i < k := by
      fin_cases i
      · exact hp.1
      · exact hp.2
    show ((((x i).val + sel p i * M : ℕ)) : ZMod (k * M)).val = _
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (add_mul_lt_mul hs (ZMod.val_lt (x i)))
  rw [sg, ← GlobalTheory.KZDist.siegel_distribution Ω ε X c k (toQ M x) (siegel_admissible_to_rat c M hc h6 hM hcM x hx) hk hck,
    ← Finset.prod_product']
  refine Finset.prod_nbij' (fun x' => ((x' 0).val / M, (x' 1).val / M)) j ?_ ?_ ?_ ?_ ?_
  · intro x' _
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨qlt x' 0, qlt x' 1⟩
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    funext i
    apply ZMod.val_injective
    rw [dn_val, jval p hp i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (ZMod.val_lt (x i))]
  · intro x' hx'
    rw [Finset.mem_filter] at hx'
    funext i
    have e := split x' hx'.2 i
    show ((((x i).val + sel _ i * M : ℕ)) : ZMod (k * M)) = x' i
    have hsel : sel ((x' 0).val / M, (x' 1).val / M) i = (x' i).val / M := by
      fin_cases i <;> rfl
    rw [hsel, ← e, ZMod.natCast_zmod_val]
  · intro p hp
    have h0 := jval p hp 0
    have h1 := jval p hp 1
    have v0 := ZMod.val_lt (x 0)
    have v1 := ZMod.val_lt (x 1)
    rw [h0, h1]
    ext
    · show ((x 0).val + p.1 * M) / M = p.1
      rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v0, zero_add]
    · show ((x 1).val + p.2 * M) / M = p.2
      rw [Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt v1, zero_add]
  · intro x' hx'
    rw [Finset.mem_filter] at hx'
    have e0 := split x' hx'.2 0
    have e1 := split x' hx'.2 1
    show siegel X c (toQ (k * M) x') = _
    congr 1
    funext i
    fin_cases i
    · show ((x' 0).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 0 + (((x' 0).val / M : ℕ) : ℚ)) / k
      rw [toQ]
      generalize (x' 0).val / M = q at e0 ⊢
      rw [e0]
      push_cast
      field_simp
    · show ((x' 1).val : ℚ) / ((k * M : ℕ) : ℚ) = (toQ M x 1 + (((x' 1).val / M : ℕ) : ℚ)) / k
      rw [toQ]
      generalize (x' 1).val / M = q at e1 ⊢
      rw [e1]
      push_cast
      field_simp
end
end
