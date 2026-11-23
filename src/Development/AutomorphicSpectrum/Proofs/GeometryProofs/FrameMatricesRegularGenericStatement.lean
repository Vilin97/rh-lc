module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicIndependentOfAdjoinStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPermNormalizedMinorsStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureSmoothStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedMinorExtendsStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqual

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem inv_mem_locSub_prod {K : Type} [Field K] {Q : Type} [Fintype Q] (D : Subring K) (s : Q → K)
    (h0 : ∀ q, s q ≠ 0) (hD : ∀ q, s q ∈ D) (q : Q) : (s q)⁻¹ ∈ locSub D (∏ q, s q) := by
  classical
  have hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q' :=
    Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)
  have hne : (∏ q', s q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'
  have e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q' := by
    rw [← hprod] at hne ⊢
    have h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0 := right_ne_zero_of_mul hne
    field_simp [h0 q, h1]
  rw [e]
  exact (locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _)
    (le_locSub D _ (D.prod_mem fun q' _ => hD q'))

theorem locSub_eq_of_inverse_family : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K),
    (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) →
    A ≤ Subring.closure ((B : Set K) ∪ Set.range t) →
    B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) →
    locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  intro K _ Q _ A B t h0 hA hB hAB hBA
  have hT : (∏ q, t q) ∈ A := A.prod_mem fun q _ => hA q
  have hTi : (∏ q, t q)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    exact B.prod_mem fun q _ => hB q
  have hBle : B ≤ locSub A (∏ q, t q) := by
    refine hBA.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub A _ hx
    · exact inv_mem_locSub_prod A t h0 hA q
  have hAle : A ≤ locSub B (∏ q, t q)⁻¹ := by
    refine hAB.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub B _ hx
    · have h := inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q
      rw [Finset.prod_inv_distrib] at h
      simpa using h
  refine le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)
  · rintro x (hx | hx)
    · exact hAle hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_locSub B _ hTi
  · rintro x (hx | hx)
    · exact hBle hx
    · rw [Set.mem_singleton_iff.1 hx, inv_inv]
      exact le_locSub A _ hT

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationClosureEqualStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem _root_.GlobalTheory.T.localization_closure_equal : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K), (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) → A ≤ Subring.closure ((B : Set K) ∪ Set.range t) → B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) → locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.locSub_eq_of_inverse_family <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinors

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_lu_of_leading_minors {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F)
    (h : ∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) :
    ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧
      (∀ l, V l l = 1) ∧ Y * C = V := by
  classical
  let B : ∀ k : Fin r, Matrix (Fin ((k : ℕ) + 1)) (Fin ((k : ℕ) + 1)) F := fun k =>
    Y.submatrix (Fin.castLE k.2) (Fin.castLE k.2)
  have hB : ∀ k, IsUnit (B k).det := fun k => isUnit_iff_ne_zero.2 (h _ k.2)
  let a : ∀ k : Fin r, Fin ((k : ℕ) + 1) → F := fun k =>
    (B k)⁻¹.mulVec (Pi.single (Fin.last _) 1)
  have ha : ∀ k, (B k).mulVec (a k) = Pi.single (Fin.last _) 1 := fun k => by
    simp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hB k), Matrix.one_mulVec]
  let C : Matrix (Fin r) (Fin r) F := fun l k =>
    if hlk : (l : ℕ) < (k : ℕ) + 1 then a k ⟨l, hlk⟩ else 0
  have hV : ∀ (k : Fin r) (l : Fin ((k : ℕ) + 1)),
      (Y * C) (Fin.castLE k.2 l) k = (Pi.single (Fin.last (k : ℕ)) (1 : F) :
        Fin ((k : ℕ) + 1) → F) l := by
    intro k l
    rw [← ha k]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    symm
    refine Finset.sum_of_injOn (Fin.castLE k.2) (Fin.castLE_injective _).injOn
      (fun _ _ => Finset.mem_univ _) (fun j _ hj => ?_) (fun b _ => ?_)
    · have hjk : ¬ (j : ℕ) < (k : ℕ) + 1 := fun hlt =>
        hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
      simp only [C, dif_neg hjk, mul_zero]
    · have hb : ((Fin.castLE k.2 b : Fin r) : ℕ) < (k : ℕ) + 1 := b.2
      simp only [C, dif_pos hb]
      rfl
  refine ⟨C, Y * C, fun l k hkl => ?_, fun l k hlk => ?_, fun l => ?_, rfl⟩
  · have hn : ¬ (l : ℕ) < (k : ℕ) + 1 := by
      have : (k : ℕ) < l := hkl
      omega
    simp only [C, dif_neg hn]
  · have hlt : (l : ℕ) < (k : ℕ) + 1 := by
      have : (l : ℕ) < k := hlk
      omega
    have h1 := hV k ⟨l, hlt⟩
    have e : Fin.castLE k.2 (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) = l := by ext; simp
    have hne : (⟨l, hlt⟩ : Fin ((k : ℕ) + 1)) ≠ Fin.last (k : ℕ) := by
      intro hh
      have h2 : (l : ℕ) = k := by simpa using Fin.ext_iff.1 hh
      have : (l : ℕ) < k := hlk
      omega
    rw [e, Pi.single_eq_of_ne hne] at h1
    exact h1
  · have h1 := hV l (Fin.last (l : ℕ))
    have e : Fin.castLE l.2 (Fin.last (l : ℕ)) = l := by ext; simp
    rw [e, Pi.single_eq_same] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuDecompositionOfMinorsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem _root_.GlobalTheory.T.lu_decomposition_of_minors : ∀ {F : Type} [Field F] {r : ℕ} (Y : Matrix (Fin r) (Fin r) F), (∀ (k : ℕ) (hk : k ≤ r), kMinor Y k hk (Fin.castLE hk) ≠ 0) → ∃ C V : Matrix (Fin r) (Fin r) F, (∀ l k, k < l → C l k = 0) ∧ (∀ l k, l < k → V l k = 0) ∧ (∀ l, V l l = 1) ∧ Y * C = V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.exists_lu_of_leading_minors <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem exists_cell {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) F) (N : Matrix (Fin r) (Fin n) F) (hA : ∀ a b, A a b ∈ O)
    (hN : ∀ a b, N a b ∈ O) (hNA : N * A = 1) (Y : Matrix (Fin r) (Fin r) F)
    (hs : ∀ i : Fin r, ∃ J, NormAt O (A * Y) ((i : ℕ) + 1) i.2 J) :
    ∃ w : Equiv.Perm (Fin r), ∀ (k : ℕ) (hk : k ≤ r), NormAt O Y k hk (w ∘ Fin.castLE hk) := by
  refine GlobalTheory.T.exists_perm_normalized_minors O Y (fun k hk I' I => GlobalTheory.T.normalized_minor_extends O Y k hk I' I) fun k hk => ?_
  cases k with
  | zero => exact ⟨Fin.elim0, normAt_zero O Y _⟩
  | succ k =>
    obtain ⟨J, hJ⟩ := hs ⟨k, hk⟩
    exact exists_normAt O A N hA hN hNA Y _ hk J hJ

theorem big_cell_smooth : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  intro Ω _ S _ r n R O _ T M N J hRO hT hM hN hNM hJ0 hJr
  classical
  haveI : Finite (GenIx r) := by unfold GenIx; infer_instance
  set i := algebraMap Ω (GenField Ω r) with hi
  set A := ratioRing R (flagB M T) J with hAdef
  let Y : ∀ s, Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun s => (T s).map i * genU Ω r s
  let Am : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := fun s => (M s).map i
  let Nm : ∀ s, Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := fun s => (N s).map i
  have hB : ∀ s, flagB M T s = Am s * Y s := fun s => by
    show (M s * T s).map i * genU Ω r s = (M s).map i * ((T s).map i * genU Ω r s)
    rw [Matrix.map_mul, Matrix.mul_assoc]
  have hNA : ∀ s, Nm s * Am s = 1 := fun s => by
    show (N s).map i * (M s).map i = 1
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hYN : ∀ s, Nm s * flagB M T s = Y s := fun s => by
    rw [hB, ← Matrix.mul_assoc, hNA, Matrix.one_mul]
  have hAmO : ∀ s a b, Am s a b ∈ O := fun s a b => hRO _ (hM _ _ _)
  have hNmO : ∀ s a b, Nm s a b ∈ O := fun s a b => hRO _ (hN _ _ _)

  have hw : ∀ s, ∃ w : Equiv.Perm (Fin (r s)), ∀ (k : ℕ) (hk : k ≤ r s),
      NormAt O (Y s) k hk (w ∘ Fin.castLE hk) := fun s =>
    exists_cell O (Am s) (Nm s) (hAmO s) (hNmO s) (hNA s) (Y s) fun i' => by
      refine ⟨J ⟨s, i'⟩, ?_⟩
      rw [← hB]
      exact ⟨hJ0 ⟨s, i'⟩, hJr ⟨s, i'⟩⟩
  choose w hw using hw
  have hlu := fun s => GlobalTheory.T.lu_decomposition_of_minors ((Y s).submatrix (w s) id) fun k hk => (hw s k hk).1
  choose C V hC hV0 hV1 hCV using hlu

  let v : GenIx r → GenField Ω r := fun q => V q.1 q.2.1.1 q.2.1.2
  set B := Subring.closure (((R.map i : Subring _) : Set (GenField Ω r)) ∪ Set.range v) with hBdef
  have hRB : ∀ a ∈ R, i a ∈ B := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hRA : ∀ a ∈ R, i a ∈ A := fun a ha =>
    Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
  have hVB : ∀ s l k, V s l k ∈ B := fun s l k => by
    rcases lt_trichotomy l k with h | h | h
    · rw [hV0 s l k h]; exact B.zero_mem
    · rw [h, hV1]; exact B.one_mem
    · exact Subring.subset_closure (Or.inr ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩)

  let y0 : (q : Σ s, Fin (r s)) → GenField Ω r := fun q =>
    kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 (w q.1 ∘ Fin.castLE q.2.2)
  have hy0 : ∀ q, y0 q ≠ 0 := fun q => (hw q.1 _ q.2.2).1
  have hrat : ∀ (s : S) (k : ℕ) (hk : k ≤ r s) (I : Fin k → Fin (r s)),
      kMinor (Y s) k hk (w s ∘ I) / kMinor (Y s) k hk (w s ∘ Fin.castLE hk) = kMinor (V s) k hk I :=
    fun s k hk I => ratio_eq_kMinor ((Y s).submatrix (w s) id) (C s) (V s) (hC s) (hV0 s) (hV1 s) (hCV s) k hk I
      (hw s k hk).1
  have hyB : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I / y0 q ∈ B := fun q I => by
    have e : I = w q.1 ∘ ((w q.1).symm ∘ I) := by
      ext a; simp
    rw [e]
    show kMinor (Y q.1) _ q.2.2 _ / kMinor (Y q.1) _ q.2.2 _ ∈ B
    rw [hrat]
    exact kMinor_mem B _ (hVB q.1) _ _ _
  have hPB : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / y0 q ∈ B := fun q J' => by
    rw [hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem B (Am q.1) (Y q.1) _ q.2.2 _ (fun a b => hRB _ (hM _ _ _)) (hyB q) J'
  have hPA : ∀ (q : Σ s, Fin (r s)) J', stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A :=
    fun q J' => Subring.subset_closure (Or.inr ⟨q, J', rfl⟩)
  have hyA : ∀ (q : Σ s, Fin (r s)) I, kMinor (Y q.1) ((q.2 : ℕ) + 1) q.2.2 I /
      stepMinor (flagB M T q.1) q.2 (J q) ∈ A := fun q I => by
    rw [← hYN q.1]
    exact kMinor_mul_div_mem A (Nm q.1) (flagB M T q.1) _ q.2.2 _ (fun a b => hRA _ (hN _ _ _)) (hPA q) I
  have hAO : A ≤ O := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact hRO b hb
    · exact hJr q J'

  let tq : (Σ s, Fin (r s)) → GenField Ω r := fun q => y0 q / stepMinor (flagB M T q.1) q.2 (J q)
  have htq0 : ∀ q, tq q ≠ 0 := fun q => div_ne_zero (hy0 q) (hJ0 q)
  have htqA : ∀ q, tq q ∈ A := fun q => hyA q _
  have htqB : ∀ q, (tq q)⁻¹ ∈ B := fun q => by
    show (y0 q / _)⁻¹ ∈ B
    rw [inv_div]
    exact hPB q _
  have htqO : ∀ q, (tq q)⁻¹ ∈ O := fun q => by
    show (y0 q / _)⁻¹ ∈ O
    rw [inv_div, hB, stepMinor_eq_kMinor]
    exact kMinor_mul_div_mem O (Am q.1) (Y q.1) _ q.2.2 _ (hAmO q.1) (hw q.1 _ q.2.2).2 _
  have hAB : A ≤ Subring.closure ((B : Set (GenField Ω r)) ∪ Set.range tq) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, J', rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRB b hb))
    · have e : stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) =
          (stepMinor (flagB M T q.1) q.2 J' / y0 q) * tq q := by
        show _ = _ * (y0 q / _)
        have := hy0 q
        have := hJ0 q
        field_simp
      rw [SetLike.mem_coe, e]
      exact mul_mem (Subring.subset_closure (Or.inl (hPB q J'))) (Subring.subset_closure (Or.inr ⟨q, rfl⟩))
  have hBA : B ≤ Subring.closure ((A : Set (GenField Ω r)) ∪ Set.range fun q => (tq q)⁻¹) := by
    refine Subring.closure_le.2 ?_
    rintro a (⟨b, hb, rfl⟩ | ⟨q, rfl⟩)
    · exact Subring.subset_closure (Or.inl (hRA b hb))
    · obtain ⟨s, ⟨⟨l, k⟩, hlk⟩⟩ := q
      have hlk' : k < l := hlk
      have e1 : V s l k = kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) / y0 ⟨s, k⟩ := by
        rw [← kMinor_lower_lastRow (V s) (hV0 s) (hV1 s) k l hlk', ← hrat]
      have e2 : V s l k = (kMinor (Y s) ((k : ℕ) + 1) k.2 (w s ∘ lastRow k l) /
          stepMinor (flagB M T s) k (J ⟨s, k⟩)) * (tq ⟨s, k⟩)⁻¹ := by
        rw [e1]
        show _ = _ * (y0 ⟨s, k⟩ / _)⁻¹
        have := hy0 ⟨s, k⟩
        have := hJ0 ⟨s, k⟩
        field_simp
      show V s l k ∈ _
      rw [e2]
      exact mul_mem (Subring.subset_closure (Or.inl (hyA ⟨s, k⟩ _))) (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

  have hv : AlgebraicIndependent Ω v := by
    refine GlobalTheory.T.algebraic_independent_of_adjoin _ v (genU_indep Ω r) fun q => ?_
    rw [← genU_gen]
    have hmem : ∀ s l k, V s l k ∈ IntermediateField.adjoin Ω (Set.range v) := fun s l k => by
      rcases lt_trichotomy l k with h | h | h
      · rw [hV0 s l k h]; exact zero_mem _
      · rw [h, hV1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, ⟨(l, k), h⟩⟩, rfl⟩
    refine entries_mem _ ((T q.1).submatrix (w q.1) id) ?_ (genU Ω r q.1) (C q.1) (V q.1)
      (genU_zero Ω r q.1) (genU_one Ω r q.1) (hC q.1) (hV0 q.1) (hV1 q.1) ?_ (hmem q.1) _ _ q.2.2
    · rw [Matrix.det_permute]
      exact mul_ne_zero (by rcases Int.units_eq_one_or (Equiv.Perm.sign (w q.1)) with h | h <;> simp [h]) (hT _)
    · rw [← hCV q.1]
      congr 1

  have hL := GlobalTheory.T.localization_closure_equal A B tq htq0 htqA htqB hAB hBA
  have htA : (∏ q, tq q) ∈ A := A.prod_mem fun q _ => htqA q
  have hinv : (∏ q, tq q)⁻¹ = ∏ q, (tq q)⁻¹ := (Finset.prod_inv_distrib _).symm
  refine ⟨∏ q, tq q, htA, Finset.prod_ne_zero_iff.2 fun q _ => htq0 q, hAO htA, ?_, ?_⟩
  · rw [hinv]
    exact O.prod_mem fun q _ => htqO q
  have hR : ∀ a ∈ R, i a ∈ locSub A (∏ q, tq q) := fun a ha => le_locSub _ _ (hRA a ha)
  refine ⟨hR, ?_⟩
  have gen : ∀ (L : Subring (GenField Ω r)), L = locSub B (∏ q, tq q)⁻¹ → ∀ h : ∀ a ∈ R, i a ∈ L,
      ((i.comp R.subtype).codRestrict L (fun a => h a a.2)).Smooth := by
    rintro _ rfl h
    refine GlobalTheory.T.localization_closure_smooth R v hv _ ?_ (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun q _ => htq0 q)) h
    rw [hinv]
    exact B.prod_mem fun q _ => htqB q
  exact gen _ hL hR

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGenericStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.frame_matrices_regular_generic : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth <;> assumption)
end
end
