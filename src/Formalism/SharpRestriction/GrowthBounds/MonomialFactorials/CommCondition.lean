module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.MahlerMeasure.LevelSum
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBSelfAdj

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem foldr_comm_of (φ : ι → V →ₗ[K] V) (ψ : V →ₗ[K] V) (l : List ι) (h : ∀ j ∈ l, ∀ x, ψ (φ j x) = φ j (ψ x))
    (x : V) : ψ ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) x) = (l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) (ψ x) := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk]))]

theorem foldr_selfAdj (B : V → V → K) (hB : ∀ a b, B a b = B b a) (φ : ι → V →ₗ[K] V) (l : List ι)
    (hs : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a)
    (hc : l.Pairwise (fun i j => ∀ x, φ i (φ j x) = φ j (φ i x))) (a b : V) :
    B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) a) b = B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) b) a := by
  induction l generalizing a b with
  | nil => simpa using hB a b
  | cons j l ih =>
    rw [List.pairwise_cons] at hc
    have hsl : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a := fun i hi => hs i (by simp [hi])
    have hcomm := foldr_comm_of φ (φ j) l (fun i hi x => (hc.1 i hi x)) b
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [hs j (by simp), hB, ih hsl hc.2, hcomm]

end Gen

def RestTieComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : Formalism.GM.M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ) (i i' : Fin G.T.t), i ≠ i' → ∀ x : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
                (G.T.z i)
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
          (G.T.z i') x) =
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
                (G.T.z i')
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
          (G.T.z i) x)

theorem phisB_selfAdj (hT : RestTieComm) (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)
    (hG : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v = Formalism.GM.M.fockK (phisB p (r := r) G j jp v) u := by
  have hfk : ∀ F G : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.M.fockK F G = Formalism.GM.M.fock p F G := fun F G => rfl
  unfold phisB
  rw [hfk, hfk]
  refine foldr_selfAdj (fun a b => Formalism.GM.M.fock p a b) (fun a b => by apply Formalism.GM.GammaExpansion.fock_comm) _ _
    (fun i _ a b => by apply Formalism.GM.GammaExpansion.fock_phi_symm) ?_ u v
  refine (List.nodup_finRange G.T.t).pairwise_of_forall_ne fun i _ i' _ hii' x => ?_
  exact hT p N r G hG j jp i i' hii' x

theorem restSymm_of (hT : RestTieComm) (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestSymm C0 CE1 CE2 X := by
  intro dl _ aTop _ x _ u _ v _
  unfold bePhi
  congr 1
  exact phisB_selfAdj hT X.p _ (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) _ _ u v

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommuteEPderiv

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Comm

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

theorem pderiv_mul_free (v : σ) (g f : MvPolynomial σ ℚ_[p]) (hg : pderiv v g = 0) :
    pderiv v (g * f) = g * pderiv v f := by
  rw [Derivation.leibniz, hg, smul_zero, add_zero, smul_eq_mul]

theorem pderiv_pair_free (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    pderiv v (∑ c, X (w c) * X (e c) : MvPolynomial σ ℚ_[p]) = 0 := by
  classical

  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_eq_of_ne (he c), Pi.single_eq_of_ne (hw c)]
  simp

theorem commute_E_pderiv (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * pderiv v f = pderiv v ((∑ c, X (w c) * X (e c)) * f)
  rw [pderiv_mul_free v _ f (pderiv_pair_free w e v hw he)]

theorem commute_E_F (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact (commute_E_pderiv w e (w' c') (fun c => h1 c c') (fun c => h2 c c')).mul_right
    (commute_E_pderiv w e (e' c') (fun c => h3 c c') (fun c => h4 c c'))

theorem commute_E_E (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieE (k := ℚ_[p]) w' e') := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * ((∑ c, X (w' c) * X (e' c)) * f) =
    (∑ c, X (w' c) * X (e' c)) * ((∑ c, X (w c) * X (e c)) * f)
  ring


theorem commute_F_F (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieF (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  have h1 : Commute (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (e' c'))
  have h2 : Commute (pderiv (e c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (e' c'))
  exact h1.mul_left h2

theorem commute_tiePhi (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') (o n z o' n' z' : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.tiePhi w e o n z (Formalism.GM.tiePhi w' e' o' n' z' x) = Formalism.GM.tiePhi w' e' o' n' z' (Formalism.GM.tiePhi w e o n z x) := by
  have cEE := commute_E_E (p := p) w e w' e'
  have cFF := commute_F_F (p := p) w e w' e'
  have cEF := commute_E_F (p := p) w e w' e' h1 h2 h3 h4
  have cFE := (commute_E_F (p := p) w' e' w e (fun c c' => (h1 c' c).symm) (fun c c' => (h3 c' c).symm)
    (fun c c' => (h2 c' c).symm) (fun c c' => (h4 c' c).symm)).symm
  have cP : Commute (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) (Formalism.GM.tiePhi (k := ℚ_[p]) w' e' o' n' z') := by
    unfold Formalism.GM.tiePhi
    refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => ?_
    refine (Commute.smul_left ?_ _).smul_right _
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact ((cEE.pow_pow j j').mul_right (cEF.pow_pow j j')).mul_left ((cFE.pow_pow j j').mul_right (cFF.pow_pow j j'))
  exact LinearMap.congr_fun cP.eq x

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommCondition

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem inl_ne {N r t : ℕ} (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) (c c' : Fin r) :
    (Sum.inl (Formalism.GM.M.finPos N a, c) : Formalism.GM.M.BVar N r t) ≠ Sum.inl (Formalism.GM.M.finPos N b, c') := by
  intro h
  have h2 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  simp only [Formalism.GM.M.finPos] at h2
  rw [min_eq_left ha.le, min_eq_left hb.le] at h2
  exact hab h2

theorem commCondition : RestTieComm := by
  intro p _ N r _ G hG j jp i i' hii' x
  obtain ⟨⟨hmono, hvec, -⟩, hlt, -, -⟩ := hG
  have hpN : ∀ k, G.T.pos k + 1 < N := fun k => (hlt k).trans G.uPos.isLt
  have hne : G.T.pos i ≠ G.T.pos i' := hmono.injective.ne hii'
  have hcross : ∀ a b : Fin G.T.t, G.T.pos a + 1 ≠ G.T.pos b := by
    intro a b hab
    obtain ⟨ha, -, ha2⟩ := hvec a
    obtain ⟨hb, hb1, -⟩ := hvec b
    have e : G.LL.vec ⟨G.T.pos a + 1, ha⟩ = G.LL.vec ⟨G.T.pos b, by omega⟩ :=
      congrArg G.LL.vec (Fin.ext hab)
    rw [e] at ha2
    exact absurd (hb1.symm.trans ha2) (by decide)
  exact commute_tiePhi _ _ _ _
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (by have := hpN i'; omega) hne c c')
    (fun c c' => inl_ne _ _ (hpN i) (by have := hpN i'; omega) (hcross i i') c c')
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (hpN i') (hcross i' i).symm c c')
    (fun c c' => inl_ne _ _ (hpN i) (hpN i') (fun h => hne (by omega)) c c')
    _ _ _ _ _ _ x

theorem symmCondition (C0 CE1 CE2 : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst) : RestSymm C0 CE1 CE2 X :=
  restSymm_of commCondition C0 CE1 CE2 X

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
