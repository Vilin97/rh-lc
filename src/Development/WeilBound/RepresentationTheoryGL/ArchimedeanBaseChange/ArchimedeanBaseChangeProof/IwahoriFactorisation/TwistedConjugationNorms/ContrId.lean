module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialOfConjTorus
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteriaStatement
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.IwFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.TlContrOf

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTorusCommutative

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.TorComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones_eq (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [ones] at this
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [ones, hi]

theorem offDiag_of_mem {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  apply GlobalTheory.CompanionTheory.LbElem.ConjMonomial.tor_offDiag <;> assumption

theorem diag_ne_zero {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  have hM : (x : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun l => (x : Matrix (Fin N) (Fin N) k) l l := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact h a b hab
  have hdet : (x : Matrix (Fin N) (Fin N) k).det ≠ 0 := (Matrix.isUnits_det_units x).ne_zero
  rw [hM, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem mem_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  apply GlobalTheory.CompanionTheory.LbElem.ConjMonomial.mem_tor_of_offDiag <;> assumption

theorem eq_diagonal {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact h a b hab

theorem mul_comm_of_mem {N : ℕ} {a b : GL (Fin N) k} (ha : a ∈ Tor k N) (hb : b ∈ Tor k N) :
    a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    eq_diagonal (a : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem ha hij),
    eq_diagonal (b : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem hb hij),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem tor_comm_and_mem_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ),
    (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧
      ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔
        ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  intro k _ _ _ _ N
  exact ⟨fun a ha b hb => mul_comm_of_mem ha hb,
    fun x => ⟨fun hx i j hij => offDiag_of_mem hx hij, mem_of_offDiag x⟩⟩

end GlobalTheory.CompanionTheory.LbElem.TorComm

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTorusCommutativeStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel

theorem _root_.GlobalTheory.T.diagonal_torus_commutative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ), (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧ ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔ ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LbElem.TorComm.tor_comm_and_mem_iff | exact GlobalTheory.CompanionTheory.LbElem.TorComm.tor_comm_and_mem_iff | (intros; apply GlobalTheory.CompanionTheory.LbElem.TorComm.tor_comm_and_mem_iff <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.ThetaFacts

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep GlobalTheory.SmGL
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem thL_eq_thetaGL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : thL n w = GlobalTheory.CuspRep.thetaGL n (cj w) := by
  unfold thL
  rw [if_neg hw]

theorem cj_cj' (w : Pl E) (x : w.adicCompletion E) : cj w (cj w x) = x := (GlobalTheory.T.localConjugation_involutive_valuation_preserving E w).1 x

theorem v_cj' (w : Pl E) (x : w.adicCompletion E) : Valued.v (cj w x) = Valued.v x := (GlobalTheory.T.localConjugation_involutive_valuation_preserving E w).2 x

theorem continuous_cj' (w : Pl E) : Continuous (cj w) := by
  unfold cj
  split_ifs with h
  · exact h.choose_spec.1
  · exact continuous_id

theorem thL_apply (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (g : GLw n w) (i j : Fin n) :
    (thL n w g).val i j = (-1) ^ ((i : ℕ) + j) * cj w ((g⁻¹).val j.rev i.rev) := by
  rw [thL_eq_thetaGL w hw]
  exact GlobalTheory.ThetaPull.thetaGL_apply _ g i j

theorem thL_invol (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) (g : GLw n w) : thL n w (thL n w g) = g := by
  rw [thL_eq_thetaGL w hw]
  exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj' w) g

theorem continuous_thL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : Continuous (thL n w) := by
  rw [thL_eq_thetaGL w hw]
  exact GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_cj' w)

def thLAut (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : MulAut (GLw n w) where
  toFun := thL n w
  invFun := thL n w
  left_inv := thL_invol w hw n
  right_inv := thL_invol w hw n
  map_mul' := (thL n w).map_mul

theorem thLAut_sq (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : thLAut w hw n ^ 2 = 1 := by
  refine MulEquiv.ext fun g => ?_
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  exact thL_invol w hw n g

theorem continuous_thLAut (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) : Continuous (thLAut w hw n) :=
  continuous_thL w hw n

section Entries

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones' (N : ℕ) (a : Fin N) (i : Fin (PositivityTheory.Lbc.ones N a)) :
    stdBlocks (PositivityTheory.Lbc.ones N) (PositivityTheory.Lbc.sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [PositivityTheory.Lbc.ones] at this
    omega
  simp [PositivityTheory.Lbc.ones, hi]

def zeroOne (N : ℕ) (a : Fin N) : Fin (PositivityTheory.Lbc.ones N a) := ⟨0, by simp [PositivityTheory.Lbc.ones]⟩

theorem nup_entries {N : ℕ} {g : GL (Fin N) k} (hg : g ∈ PositivityTheory.Lbc.Nup k N) :
    (∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := (mem_parab_iff.1 h1) i j (zeroOne N i) (zeroOne N j) hij
    rwa [stdBlocks_ones', stdBlocks_ones'] at this
  · have := h2 i (zeroOne N i) (zeroOne N i)
    rwa [stdBlocks_ones', Matrix.one_apply_eq] at this

theorem nlo_entries {N : ℕ} {g : GL (Fin N) k} (hg : g ∈ PositivityTheory.Lbc.Nlo k N) :
    (∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1 := by
  obtain ⟨h1, h2⟩ := (mem_unipRadLower k).1 hg
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := ((mem_parabLower_iff k).1 h1) i j (zeroOne N i) (zeroOne N j) hij
    rwa [stdBlocks_ones', stdBlocks_ones'] at this
  · have := h2 i (zeroOne N i) (zeroOne N i)
    rwa [stdBlocks_ones', Matrix.one_apply_eq] at this

theorem mem_Nup_of' {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, j < i → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ PositivityTheory.Lbc.Nup k N := by
  refine mem_unipRad.2 ⟨mem_parab_iff.2 fun a b i j hab => ?_, fun a i j => ?_⟩
  · rw [stdBlocks_ones', stdBlocks_ones']
    exact h0 a b hab
  · have hij : i = j := Fin.ext (by have := i.2; have := j.2; simp only [PositivityTheory.Lbc.ones] at *; omega)
    subst hij
    rw [stdBlocks_ones', h1, Matrix.one_apply_eq]

theorem mem_Nlo_of' {N : ℕ} (g : GL (Fin N) k)
    (h0 : ∀ i j : Fin N, i < j → (g : Matrix (Fin N) (Fin N) k) i j = 0)
    (h1 : ∀ i, (g : Matrix (Fin N) (Fin N) k) i i = 1) : g ∈ PositivityTheory.Lbc.Nlo k N := by
  refine (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j hab => ?_, fun a i j => ?_⟩
  · rw [stdBlocks_ones', stdBlocks_ones']
    exact h0 a b hab
  · have hij : i = j := Fin.ext (by have := i.2; have := j.2; simp only [PositivityTheory.Lbc.ones] at *; omega)
    subst hij
    rw [stdBlocks_ones', h1, Matrix.one_apply_eq]

end Entries

theorem neg_one_pow_add_self {R : Type} [Ring R] (i : ℕ) : (-1 : R) ^ (i + i) = 1 := by
  rw [← two_mul, pow_mul, neg_one_sq, one_pow]

theorem v_sign_cj (w : Pl E) (m : ℕ) (x : w.adicCompletion E) :
    Valued.v ((-1) ^ m * cj w x) = Valued.v x := by
  rw [map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul, v_cj']

theorem thL_mem_iwGL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ iwGL n w) :
    thL n w g ∈ iwGL n w := by
  have hE := fun x : GLw n w => (GlobalTheory.T.iwahori_and_maximal_compact_criteria E w n x).1
  obtain ⟨g1, g2, -⟩ := (hE g).1 hg
  obtain ⟨-, -, h3⟩ := (hE g⁻¹).1 (inv_mem hg)
  refine (hE _).2 ⟨fun i j => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [thL_apply w hw, v_sign_cj]
    exact g2 _ _
  · rw [← map_inv, thL_apply w hw, v_sign_cj, inv_inv]
    exact g1 _ _
  · rw [thL_apply w hw, v_sign_cj]
    exact h3 _ _ (Fin.rev_lt_rev.2 hij)

theorem thL_mem_Nup (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w}
    (hg : g ∈ PositivityTheory.Lbc.Nup (w.adicCompletion E) n) : thL n w g ∈ PositivityTheory.Lbc.Nup (w.adicCompletion E) n := by
  obtain ⟨h0, h1⟩ := nup_entries (inv_mem hg)
  refine mem_Nup_of' _ (fun i j hij => ?_) (fun i => ?_)
  · show (thL n w g).val i j = 0
    rw [thL_apply w hw, h0 _ _ (Fin.rev_lt_rev.2 hij), map_zero, mul_zero]
  · show (thL n w g).val i i = 1
    rw [thL_apply w hw, h1, map_one, mul_one, neg_one_pow_add_self]

theorem thL_mem_Nlo (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w}
    (hg : g ∈ PositivityTheory.Lbc.Nlo (w.adicCompletion E) n) : thL n w g ∈ PositivityTheory.Lbc.Nlo (w.adicCompletion E) n := by
  obtain ⟨h0, h1⟩ := nlo_entries (inv_mem hg)
  refine mem_Nlo_of' _ (fun i j hij => ?_) (fun i => ?_)
  · show (thL n w g).val i j = 0
    rw [thL_apply w hw, h0 _ _ (Fin.rev_lt_rev.2 hij), map_zero, mul_zero]
  · show (thL n w g).val i i = 1
    rw [thL_apply w hw, h1, map_one, mul_one, neg_one_pow_add_self]

theorem thL_mem_Tor (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w}
    (hg : g ∈ PositivityTheory.Lbc.Tor (w.adicCompletion E) n) : thL n w g ∈ PositivityTheory.Lbc.Tor (w.adicCompletion E) n := by
  have hT := fun x : GLw n w => (GlobalTheory.T.diagonal_torus_commutative (k := w.adicCompletion E) n).2 x
  have h0 := (hT g⁻¹).1 (inv_mem hg)
  refine (hT _).2 fun i j hij => ?_
  show (thL n w g).val i j = 0
  rw [thL_apply w hw, h0 _ _ (fun h => hij (Fin.rev_injective h).symm), map_zero, mul_zero]

theorem map_eq_of_invol {G : Type} [Group G] (θ : MulAut G) (hθ : ∀ g, θ (θ g) = g) (H : Subgroup G)
    (hH : ∀ g ∈ H, θ g ∈ H) : H.map θ.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hH y hy
  · intro hx
    exact ⟨θ x, hH x hx, hθ x⟩

theorem thLAut_map_iwGL (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (iwGL n w).map (thLAut w hw n).toMonoidHom = iwGL n w :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_iwGL w hw n hg

theorem thLAut_map_Nup (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (PositivityTheory.Lbc.Nup (w.adicCompletion E) n).map (thLAut w hw n).toMonoidHom = PositivityTheory.Lbc.Nup (w.adicCompletion E) n :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_Nup w hw n hg

theorem thLAut_map_Nlo (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (PositivityTheory.Lbc.Nlo (w.adicCompletion E) n).map (thLAut w hw n).toMonoidHom = PositivityTheory.Lbc.Nlo (w.adicCompletion E) n :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_Nlo w hw n hg

theorem thLAut_map_Tor (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    (PositivityTheory.Lbc.Tor (w.adicCompletion E) n).map (thLAut w hw n).toMonoidHom = PositivityTheory.Lbc.Tor (w.adicCompletion E) n :=
  map_eq_of_invol _ (thL_invol w hw n) _ fun _ hg => thL_mem_Tor w hw n hg

theorem thL_tdiag (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : cj w (ϖ : w.adicCompletion E) = ϖ) (n : ℕ) (y : Fin n → ℤ) :
    thL n w (tdiag ϖ y) = tdiag ϖ (fun i => -y i.rev) := by
  apply Units.ext
  ext i j
  rw [thL_apply w hw]
  unfold tdiag
  rw [← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, diagonal_apply_eq]
    simp only [Pi.inv_apply]
    rw [← _root_.zpow_neg, Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, neg_one_pow_add_self, one_mul]
  · rw [diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), diagonal_apply_ne _ h, map_zero, mul_zero]

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.TlContr

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem iwahori_unitary_involution_admissible (w : Pl E) (hw : ¬ IsSplitAt w) (n : ℕ) :
    PositivityTheory.Lbc.admitted (w.adicCompletion E) n (iwGL n w) (thLAut w hw n) 2 :=
  ⟨iw_isOpen n, iw_isCompact n, iw_hasIwahoriFact n, continuous_thLAut w hw n, two_pos, thLAut_sq w hw n,
    thLAut_map_iwGL w hw n, thLAut_map_Nup w hw n, thLAut_map_Nlo w hw n, thLAut_map_Tor w hw n⟩

theorem contr_tw_tl (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ)
    (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * thL n w m = tdiag ϖ y * τ :=
  tl_contr_of w ϖ hϖ.1 n (thLAut w hw n) (iwahori_unitary_involution_admissible w hw n) y hy (thL_tdiag w hw ϖ hϖ.2 n y) δ hδ

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.ContrId

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem contr_tw (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) (n : ℕ)
    (y : Fin n → ℤ) (hy : StrictAnti y) (δ : GLw n w) (hδ : dcos n w (tdiag ϖ y) δ ≠ 0) :
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * thL n w m = tdiag ϖ y * τ := by
  exact contr_tw_tl hU w hw ϖ hϖ n y hy δ hδ

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
end
end
end
