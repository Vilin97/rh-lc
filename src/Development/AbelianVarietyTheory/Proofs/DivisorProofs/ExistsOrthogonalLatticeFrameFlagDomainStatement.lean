module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianTraceFormVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT
import Mathlib.Algebra.Order.Star.Real
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomain

section

@[expose] public section

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame.GramSchmidt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sum_left (G : Matrix (Fin r) (Fin r) E) (s : Finset (Fin r)) (f : Fin r → E)
    (w : Fin r → Fin r → E) (y : Fin r → E) :
    herm G (∑ j ∈ s, f j • w j) y = ∑ j ∈ s, f j * herm G (w j) y := by
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, ih]

theorem psi_nonempty (X : Data E r) : ∃ τ, τ ∈ X.Ψ := by
  let τ0 : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  by_cases h : τ0 ∈ X.Ψ
  · exact ⟨τ0, h⟩
  · exact ⟨_, not_not.mp (mt (X.cmType τ0).2 h)⟩

theorem dmin_frm_of_lt (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (i : Fin (r + 1))
    (ho : ∀ j k : Fin r, (j : ℕ) < i → (k : ℕ) < i → j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (by rw [Fin.coe_castLE]; exact a.isLt) (by rw [Fin.coe_castLE]; exact b.isLt)
        (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem herm_self_ne (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : ℕ)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (j : Fin r) (hj : (j : ℕ) < m) : herm X.Gm (v j) (v j) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := psi_nonempty X
  have h1 := (hv ⟨τ, hτ⟩).2 j.succ
  have hd : dmin X.Gm (frm X.Ψ v) ⟨τ, hτ⟩ j.succ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [dmin_frm_of_lt X.Ψ X.Gm v j.succ (fun a b ha hb hab => ho a b
    (by simp only [Fin.val_succ] at ha; omega) (by simp only [Fin.val_succ] at hb; omega) hab)] at hd
  have hf := Finset.prod_ne_zero_iff.mp hd ⟨j, by simp⟩ (Finset.mem_univ _)
  have he : (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) ⟨(j : ℕ), by simp⟩ : Fin r) = j := Fin.ext rfl
  rw [he] at hf
  intro h0
  exact hf (by rw [h0, map_zero])

def gsMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Matrix (Fin r) (Fin r) E :=
  fun j a => (if j = a then 1 else 0) -
    (if a = m ∧ j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0)

def gsStep (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Fin r → Fin r → E :=
  fun a k => ∑ j, v j k * gsMat G v m j a

theorem gsStep_ne (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m a : Fin r)
    (h : a ≠ m) : gsStep G v m a = v a := by
  funext k
  simp [gsStep, gsMat, h]

theorem gsStep_self (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    gsStep G v m m = v m - ∑ j, (if j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0) • v j := by
  funext k
  simp only [gsStep, gsMat, true_and, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem frm_gsStep (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : frm Ψ (gsStep G v m) = rmul (frm Ψ v) (fun τ j a => τ.1 (gsMat G v m j a)) := by
  funext τ k a

  simp [frm, rmul, mat, Matrix.mul_apply, gsStep, map_sum, map_mul]

theorem gsB_mem (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) ∈ Bor Ψ r := by
  have hlow : ∀ a c : Fin r, c < a → gsMat G v m a c = 0 := by
    intro a c hca
    have h1 : a ≠ c := fun h => lt_irrefl _ (h ▸ hca)
    have h2 : ¬ (c = m ∧ a < m) := fun h => lt_asymm hca (h.1 ▸ h.2)
    simp [gsMat, h1, h2]
  intro τ
  refine ⟨?_, fun a c hca => by simp [hlow a c hca]⟩
  have ht : (mat (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) τ).BlockTriangular id := by
    intro a c hca
    simp [mat, hlow a c hca]
  rw [Matrix.det_of_upperTriangular ht]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have hn : ¬ (a = m ∧ a < m) := by rintro ⟨rfl, h⟩; exact lt_irrefl _ h
  simp [mat, gsMat, hn]

theorem herm_gsStep_self (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : Fin r)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (k : Fin r) (hk : k < m) : herm X.Gm (gsStep X.Gm v m m) (v k) = 0 := by
  have hkm : (k : ℕ) < m := hk
  have hne := herm_self_ne X v hv m ho k hkm
  rw [gsStep_self, HermitianTraceFormVanishing.herm_sub_left, herm_sum_left,
    Finset.sum_eq_single k (fun i _ hik => ?_) (fun h => absurd (Finset.mem_univ k) h),
    if_pos hk, div_mul_cancel₀ _ hne, sub_self]
  split_ifs with him
  · rw [ho i k him hkm hik, mul_zero]
  · rw [zero_mul]

theorem exists_ortho_lt (X : Data E r) (u : Fin r → Fin r → E) (hu : frm X.Ψ u ∈ X.dom) :
    ∀ m ≤ r, ∃ v : Fin r → Fin r → E, frm X.Ψ v ∈ X.dom ∧
      ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨u, hu, fun j k hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hv, ho⟩ := ih (Nat.le_of_succ_le hm)
    let mf : Fin r := ⟨m, hm⟩
    refine ⟨gsStep X.Gm v mf, ?_, ?_⟩
    · rw [frm_gsStep]
      exact OrthogonalFrameDomain.rmul_mem_dom X hv (gsB_mem X.Ψ X.Gm v mf)
    · intro j k hj hk hjk
      by_cases hjm : j = mf
      · have hkm : k ≠ mf := fun h => hjk (hjm.trans h.symm)
        have hk' : k < mf := by
          rw [Fin.lt_iff_val_lt_val]
          have : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          show (k : ℕ) < m
          omega
        rw [hjm, gsStep_ne X.Gm v mf k hkm]
        exact herm_gsStep_self X v hv mf ho k hk'
      · by_cases hkm : k = mf
        · have hj' : j < mf := by
            rw [Fin.lt_iff_val_lt_val]
            have : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
            show (j : ℕ) < m
            omega
          rw [hkm, gsStep_ne X.Gm v mf j hjm, ← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm,
            herm_gsStep_self X v hv mf ho j hj', HermitianTraceFormVanishing.cc_zero]
        · rw [gsStep_ne X.Gm v mf j hjm, gsStep_ne X.Gm v mf k hkm]
          have hj' : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
          have hk' : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          exact ho j k (by omega) (by omega) hjk

theorem exists_ortho_frm (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E) :
    GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E,
      (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  intro hu
  obtain ⟨v, hv, ho⟩ := exists_ortho_lt X u hu r le_rfl
  exact ⟨v, fun j k hjk => ho j k j.isLt k.isLt hjk, hv⟩

end

end GlobalTheory.OrthoFrame.GramSchmidt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomainStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E), GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E, (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | exact GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | (intros; apply GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomain

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.OrthoFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_approx_cmType (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : Ψ → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : E, ∀ τ : Ψ, dist (w τ) (τ.1 x) < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  choose z hz using fun τ : Ψ => Metric.denseRange_iff.1
    (GlobalTheory.ShortVec.denseRange_emb τ.1 (IsTotallyComplex.complexEmbedding_not_isReal τ.1)) (w τ) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (v := fun τ : Ψ => (InfinitePlace.mk τ.1).1) (fun τ => InfinitePlace.isNontrivial _)
    (by
      intro σ τ hne h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.eq_iff_isEquiv.2 h) with h1 | h1
      · exact hne (Subtype.ext h1)
      · exact (hΨ σ.1).1 σ.2 (h1 ▸ τ.2)) z hε2
  refine ⟨x, fun τ => ?_⟩
  have h1 : ‖τ.1 (z τ - x)‖ < ε / 2 := by
    rw [← InfinitePlace.apply]; exact hx τ
  rw [map_sub, ← dist_eq_norm] at h1
  have h2 := dist_triangle (w τ) (τ.1 (z τ)) (τ.1 x)
  have h3 := hz τ
  linarith

theorem dom_nonempty {r : ℕ} (X : Data E r) : X.dom.Nonempty := by
  choose P hP using X.signature
  refine ⟨fun τ k a => P τ k a, fun τ => ⟨(hP τ).1, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ k a => P τ k a) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    change lminor (gram τ.1 X.Gm (P τ)) i = _
    rw [(hP τ).2, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  unfold sgn
  split_ifs <;> norm_num

theorem exists_frm_mem_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r),
    ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  intro E _ _ _ r X
  obtain ⟨P, hP⟩ := dom_nonempty X
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (FourierCoefficientDomain.isOpen_dom X) P hP
  choose u hu using fun a k : Fin r =>
    exists_approx_cmType X.Ψ X.cmType (fun τ => P τ k a) hε
  refine ⟨u, hb ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_pi_lt_iff hε]
  intro τ
  rw [dist_pi_lt_iff hε]
  intro k
  rw [dist_pi_lt_iff hε]
  intro a
  exact hu a k τ

end GlobalTheory.OrthoFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomainStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_rational_frame_mem_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.exists_frm_mem_dom | exact GlobalTheory.OrthoFrame.exists_frm_mem_dom | (intros; apply GlobalTheory.OrthoFrame.exists_frm_mem_dom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomain

section

@[expose] public section

open NumberField

namespace GlobalTheory.OrthoFrame

theorem exists_orthoFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  intro E _ _ _ r X
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_rational_frame_mem_flagDomain E r X
  obtain ⟨v, ho, hv⟩ := GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain E r X u hu
  have hs := GlobalTheory.OrthoFrame.sign_of_mem X v ho hv
  choose d hd0 hdΛ using fun j => ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.exists_smul_mem X.Λ (x := v j)
    (by rw [X.Λ_span]; exact Submodule.mem_top)
  have hd0' : ∀ j, ((d j : 𝓞 E) : E) ≠ 0 := fun j h => hd0 j (by exact_mod_cast h)
  set lam : Fin r → Fin r → E := fun j => ((d j : 𝓞 E) : E) • v j with hlam
  have hlamΛ : ∀ j, lam j ∈ X.Λ := fun j => by
    have e : (d j) • v j = ((d j : 𝓞 E) : E) • v j := by
      ext a; simp [Algebra.smul_def]
    rw [hlam]; dsimp only; rw [← e]; exact hdΛ j
  have hlo : ∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0 := by
    intro j k h
    simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, ho j k h,
      mul_zero]
  have hsl : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
      (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re := by
    intro τ j
    have hn : 0 < Complex.normSq (τ.1 (d j : E)) := Complex.normSq_pos.2 ((map_ne_zero τ.1).2 (hd0' j))
    have e : τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j)) =
        (Complex.normSq (τ.1 (d j : E)) : ℂ) * τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j)) := by
      simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, map_mul,
        GlobalTheory.OrthoFrame.emb_cc, ← Complex.mul_conj]
      ring
    rw [e, Complex.re_ofReal_mul]
    have := hs τ j
    calc (0 : ℝ) < Complex.normSq (τ.1 (d j : E)) * (ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
        (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j))).re) := mul_pos hn this
      _ = _ := by ring
  have hΨ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, ?_⟩
      by_contra h'
      exact h ((X.cmType τ0).2 h')
  obtain ⟨τ0, hτ0⟩ := hΨ
  have hdv : (Matrix.of v).det ≠ 0 := by
    have h := (hv ⟨τ0, hτ0⟩).1
    have e : ReciprocityTheory.ChartRestriction.G.FD.mat (GlobalTheory.OrthoFrame.frm X.Ψ v) ⟨τ0, hτ0⟩ = τ0.mapMatrix (Matrix.of v).transpose := by
      ext k a; rfl
    rw [e, ← RingHom.map_det, Matrix.det_transpose] at h
    intro h0; exact h (by rw [h0, map_zero])
  have hdl : (Matrix.of lam).det ≠ 0 := by
    have e : Matrix.of lam = Matrix.diagonal (fun j => ((d j : 𝓞 E) : E)) * Matrix.of v := by
      ext j k; simp only [hlam, Matrix.of_apply, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd0' j) hdv
  refine ⟨GlobalTheory.OrthoFrame.frm X.Ψ lam, GlobalTheory.OrthoFrame.mem_of_sign X lam hlo hdl hsl, lam, hlamΛ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_of_det_ne_zero hdl
  · intro j k hj hk
    exact hlo j k (by intro h; subst h; omega)
  · intro j hj τ
    have := hsl τ j
    simpa [ReciprocityTheory.ChartRestriction.G.FD.sgn, hj] using this
  · intro j hj τ
    have := hsl τ j
    simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg (not_lt.2 hj)] at this
    linarith
  · intro τ
    rfl

end GlobalTheory.OrthoFrame
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomainStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  first | exact @GlobalTheory.OrthoFrame.exists_orthoFrame | exact GlobalTheory.OrthoFrame.exists_orthoFrame | (intros; apply GlobalTheory.OrthoFrame.exists_orthoFrame <;> assumption)
end
end
