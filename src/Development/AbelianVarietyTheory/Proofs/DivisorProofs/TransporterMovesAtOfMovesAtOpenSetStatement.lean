module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranspOfMovesAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCandidateBorelMoveOpenFramesBaire

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

noncomputable section

theorem countable_GL_numberField {E : Type} [Field E] [NumberField E] (r : ℕ) :
    Countable (GL (Fin r) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable
    (f := fun g : GL (Fin r) E => (g : Matrix (Fin r) (Fin r) E)) fun _ _ h => Units.ext h

theorem continuous_mat_lact {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (g : GL (Fin r) E) (τ : Ψ) :
    Continuous fun z : Frame Ψ r => mat (lact g z) τ := by
  have h : Continuous fun z : Frame Ψ r => mat z τ := continuous_apply τ
  exact continuous_const.matrix_mul h

theorem baire_one_candidate {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)) :
    IsOpen W → W.Nonempty → W ⊆ X.dom →
    (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) →
    ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧
      ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  intro hW hne hWdom hmove
  let C : GL (Fin r) E → Set (Frame X.Ψ r) := fun g => {z | ∀ τ : X.Ψ, ∀ p q : Fin r, q < p →
    ((mat (lact (g * a) z) τ).adjugate * mat (lact c z) τ) p q = 0}
  have hC : ∀ g, IsClosed (C g) := by
    intro g
    simp only [C, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun p => isClosed_iInter fun q =>
      isClosed_iInter fun _ => ?_
    exact isClosed_eq ((((continuous_mat_lact (g * a) τ).matrix_adjugate).matrix_mul
      (continuous_mat_lact c τ)).matrix_elem p q) continuous_const
  have cover : ∀ z ∈ W, ∃ γ ∈ S, z ∈ C γ := by
    intro z hz
    obtain ⟨γ, hγ, b, hb, heq⟩ := hmove z hz
    refine ⟨γ, hγ, fun τ p q hqp => ?_⟩
    have key : mat (lact c z) τ = mat (lact (γ * a) z) τ * mat b τ := by
      have h1 : mat (lact c z) τ =
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((a : Matrix (Fin r) (Fin r) E).map τ.1 *
            mat z τ)) * mat b τ := congrFun heq τ
      rw [h1]
      show _ = (((γ * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ) * mat b τ
      rw [Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [key, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
    have : mat b τ p q = 0 := (hb τ).2 p q hqp
    rw [this, mul_zero]
  haveI : Countable (GL (Fin r) E) := countable_GL_numberField r
  let f : Option S → Set (Frame X.Ψ r) := fun o => o.elim Wᶜ (fun γ => C γ.1)
  have hf : ∀ o, IsClosed (f o) := by
    rintro (_ | γ)
    exacts [hW.isClosed_compl, hC γ.1]
  have hU : ⋃ o, f o = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ W
    · obtain ⟨γ, hγ, hzC⟩ := cover z hz
      exact Set.mem_iUnion.2 ⟨some ⟨γ, hγ⟩, hzC⟩
    · exact Set.mem_iUnion.2 ⟨none, hz⟩
  have hD := dense_iUnion_interior_of_closed hf hU
  obtain ⟨z, hzW, hz⟩ := hD.inter_open_nonempty W hW hne
  obtain ⟨o, ho⟩ := Set.mem_iUnion.1 hz
  cases o with
  | none => exact absurd hzW (interior_subset ho)
  | some γ =>
    refine ⟨γ.1, γ.2, W ∩ interior (C γ.1), hW.inter isOpen_interior, ⟨z, hzW, ho⟩,
      fun x hx => hWdom hx.1, fun x hx => ?_⟩
    have hxd : x ∈ X.dom := hWdom hx.1
    have hxC : x ∈ C γ.1 := interior_subset hx.2
    simp only [C, Set.mem_setOf_eq] at hxC
    generalize γ.1 * a = g at hxC ⊢
    have hdetg : ∀ (g' : GL (Fin r) E) (τ : X.Ψ),
        ((g' : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
      intro g' τ
      have h := RingHom.map_det τ.1 (g' : Matrix (Fin r) (Fin r) E)
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units g').ne_zero
    have hdetx : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun τ => (hxd τ).1
    have hdetA : ∀ (g' : GL (Fin r) E) (τ : X.Ψ), (mat (lact g' x) τ).det ≠ 0 := by
      intro g' τ
      show ((g' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hdetg g' τ) (hdetx τ)
    let b : Frame X.Ψ r := fun τ =>
      ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ : Matrix (Fin r) (Fin r) ℂ)
    refine ⟨b, fun τ => ⟨?_, fun p q hqp => ?_⟩, ?_⟩
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero
        (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 (hdetA g τ))).ne_zero (hdetA c τ)
    · show ((mat (lact g x) τ)⁻¹ * mat (lact c x) τ) p q = 0
      rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, hxC τ p q hqp, smul_zero]
    · funext τ
      have hginv : ((g : Matrix (Fin r) (Fin r) E).map τ.1)⁻¹ =
          ((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 := by
        apply Matrix.inv_eq_right_inv
        rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.map_one _ (map_zero _) (map_one _)]
      show ((g⁻¹ * c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
        mat x τ * (((g : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)⁻¹ *
          ((c : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))
      rw [Matrix.mul_inv_rev, hginv, Units.val_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (mat x τ) (mat x τ)⁻¹,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdetx τ)), Matrix.one_mul]

end

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCandidateBorelMoveOpenFramesBaireStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.exists_candidate_borel_move_open_frames_baire : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) → ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧ ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  first | exact @GlobalTheory.baire_one_candidate | exact GlobalTheory.baire_one_candidate | (intros; apply GlobalTheory.baire_one_candidate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFrames

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix

namespace GlobalTheory

theorem scalar_of_triangular_moves_open :
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  intro E _ _ _ r X m W hW hne _ hact
  classical
  cases r with
  | zero => exact ⟨0, by ext i; exact i.elim0⟩
  | succ n =>
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : ∃ τ, τ ∈ X.Ψ := by
    by_cases h : σ ∈ X.Ψ
    · exact ⟨σ, h⟩
    · refine ⟨ComplexEmbedding.conjugate σ, ?_⟩
      by_contra h'
      exact h ((X.cmType σ).2 h')
  obtain ⟨τ0, hτ0⟩ := hτ
  let τ : X.Ψ := ⟨τ0, hτ0⟩
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := (m : Matrix (Fin (n+1)) (Fin (n+1)) E).map τ0
  have key : ∀ y ∈ W, ∀ i j : Fin (n+1),
      (M *ᵥ (fun k => y τ k 0)) i * y τ j 0 = (M *ᵥ (fun k => y τ k 0)) j * y τ i 0 := by
    intro y hy i j
    obtain ⟨b, hb, he⟩ := hact y hy
    have hcol : ∀ a : Fin (n+1), (M *ᵥ (fun k => y τ k 0)) a = y τ a 0 * b τ 0 0 := by
      intro a
      have := congrFun (congrFun (congrFun he τ) a) 0
      simp only [lact, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at this
      have hs : ∑ k, y τ a k * b τ k 0 = y τ a 0 * b τ 0 0 := by
        rw [Finset.sum_eq_single (0 : Fin (n+1))]
        · intro k _ hk
          rw [(hb τ).2 k 0 (Fin.pos_of_ne_zero hk), mul_zero]
        · simp
      rw [hs] at this
      simp only [Matrix.mulVec, dotProduct]
      exact this
    rw [hcol i, hcol j]; ring
  obtain ⟨x0, hx0⟩ := hne
  have hq : ∀ w : Fin (n+1) → ℂ, ∀ i j : Fin (n+1), (M *ᵥ w) i * w j = (M *ᵥ w) j * w i := by
    intro w i j
    let pert : ℂ → Frame X.Ψ (n+1) := fun t σ a c => x0 σ a c + if σ = τ ∧ c = 0 then t * w a else 0
    have hc : Continuous pert := by
      apply continuous_pi; intro σ; apply continuous_pi; intro a; apply continuous_pi; intro c
      by_cases h : σ = τ ∧ c = 0
      · simp only [pert, h, and_self, if_true]; fun_prop
      · simp only [pert, h, if_false]; fun_prop
    have h0 : pert 0 = x0 := by funext σ a c; simp [pert]
    have hO : IsOpen (pert ⁻¹' W) := hW.preimage hc
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO 0 (by simp [h0, hx0])
    set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht_def
    have htn : t ≠ 0 := by
      rw [ht_def]; exact_mod_cast (by positivity : ε / 2 ≠ 0)
    have hnorm : ‖t‖ < ε := by
      rw [ht_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have h1 : pert t ∈ W := hball (by simpa using hnorm)
    have h2 : pert (-t) ∈ W := hball (by simpa using hnorm)
    have hcolp : ∀ s : ℂ, (fun k => pert s τ k 0) = (fun k => x0 τ k 0) + s • w := by
      intro s; funext k; simp [pert]
    have e1 := key _ h1 i j
    have e2 := key _ h2 i j
    have e0 := key _ hx0 i j
    have hpt : ∀ s : ℂ, ∀ k, pert s τ k 0 = x0 τ k 0 + s * w k := by
      intro s k; simp [pert]
    rw [hcolp] at e1 e2
    simp only [hpt, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have : t ^ 2 * ((M *ᵥ w) i * w j - (M *ᵥ w) j * w i) = 0 := by
      linear_combination (1/2 : ℂ) * e1 + (1/2 : ℂ) * e2 - e0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) htn
    · exact sub_eq_zero.mp h
  have hoff : ∀ i j : Fin (n+1), i ≠ j → M i j = 0 := by
    intro i j hij
    have := hq (Pi.single j 1) i j
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hij] using this
  have hsv : ∀ j k : Fin (n+1), (M *ᵥ Pi.single j (1:ℂ)) k = M k j := by
    intro j k; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdiag : ∀ i j : Fin (n+1), M i i = M j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have := hq (Pi.single i 1 + Pi.single j 1) i j
    have hji : j ≠ i := Ne.symm hij
    rw [Matrix.mulVec_add] at this
    simp only [Pi.add_apply, hsv, Pi.single_apply, hij, hji, if_true, if_false, mul_one, add_zero, zero_add, hoff i j hij, hoff j i hji] at this
    exact this
  refine ⟨(m : Matrix (Fin (n+1)) (Fin (n+1)) E) 0 0, ?_⟩
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply τ0.injective
    have := hdiag i 0
    simpa [M] using this
  · apply τ0.injective
    have := hoff i j hij
    simpa [M] using this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFramesStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.scalar_of_borel_moves_open_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  first | exact @GlobalTheory.scalar_of_triangular_moves_open | exact GlobalTheory.scalar_of_triangular_moves_open | (intros; apply GlobalTheory.scalar_of_triangular_moves_open <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAtOfMovesAtOpenSet

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_movesAt_open : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v γ k k' k'' a c hma hmc W hWo hWn hWd hW x hx hcx
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨-, htr, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have step : ∀ z (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W →
      ∃ γ' ∈ ((uAt r v i).X k').Γ, ∃ b ∈ Bor ((uAt r v i).X k').Ψ D.R.r,
        (⟨k'', castFrame hmc.psi (lact c z)⟩ : Σ k, Frame ((uAt r v i).X k).Ψ D.R.r) =
          ⟨k', rmul (lact γ' (castFrame hma.psi (lact a z))) b⟩ := by
    intro z hz hzW
    obtain ⟨⟨hy₁, t₁, f₁⟩, ⟨hy₂, t₂, f₂⟩⟩ := hW z hz hzW
    have hb := htr _ _ _ _ _ f₁ (hsy _ _ _ f₂)
    exact (hU.2.2.2.1 k' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).1 ⟨_, hb⟩
  obtain ⟨z₀, hz₀⟩ := hWn
  have hk : k'' = k' := by
    obtain ⟨g₀, -, b₀, -, e₀⟩ := step z₀ (hWd hz₀) hz₀
    exact (Sigma.mk.inj_iff.1 e₀).1
  subst hk
  have hcast : ∀ z (b : Frame ((uAt r v i).X k'').Ψ D.R.r) (γ' : GL (Fin D.R.r) D.host.E),
      castFrame hmc.psi (lact c z) = rmul (lact γ' (castFrame hma.psi (lact a z))) b →
      lact c z = rmul (lact γ' (lact a z)) (castFrame hma.psi.symm b) := by
    intro z b γ' e
    funext τ
    have := congrFun e ⟨τ.1, hma.psi ▸ τ.2⟩
    exact this
  have hborc : ∀ b ∈ Bor ((uAt r v i).X k'').Ψ D.R.r, castFrame hma.psi.symm b ∈ Bor ((uAt r v i).X k).Ψ D.R.r := by
    intro b hb τ
    exact hb ⟨τ.1, hma.psi ▸ τ.2⟩
  obtain ⟨γ', hγ', V, hVo, hVn, hVd, hV⟩ := GlobalTheory.T.exists_candidate_borel_move_open_frames_baire ((uAt r v i).X k) ((uAt r v i).X k'').Γ a c W hWo ⟨z₀, hz₀⟩ hWd
    (fun z hz => by
      obtain ⟨γ', hγ', b, hb, e⟩ := step z (hWd hz) hz
      exact ⟨γ', hγ', _, hborc b hb, hcast z b γ' (eq_of_heq (Sigma.mk.inj_iff.1 e).2)⟩)
  obtain ⟨s, hs⟩ := GlobalTheory.T.scalar_of_borel_moves_open_frames ((uAt r v i).X k) _ V hVo hVn hVd hV
  set m : GL (Fin D.R.r) D.host.E := (γ' * a)⁻¹ * c with hm_def
  have hcm : (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (a : Matrix _ _ _) * (m : Matrix _ _ _) := by
    have : c = γ' * a * m := by rw [hm_def]; group
    rw [this]; simp [Units.val_mul]
  obtain ⟨hy₂, t₂, f₂⟩ := hcx
  have hy₁ : castFrame hma.psi (lact a x) ∈ ((uAt r v i).X k'').dom := hma.mem_dom hx
  let bm : Frame ((uAt r v i).X k'').Ψ D.R.r := fun τ => (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
  have hbm : bm ∈ Bor ((uAt r v i).X k'').Ψ D.R.r := by
    intro τ
    refine ⟨?_, fun p q hpq => ?_⟩
    · show ((m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1).det ≠ 0
      rw [show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = τ.1.mapMatrix (m : Matrix _ _ _) from rfl,
        ← RingHom.map_det]
      have hu : IsUnit (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det :=
        (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
      exact (map_ne_zero τ.1).2 hu.ne_zero
    · show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 p q = 0
      rw [hs, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (ne_of_lt hpq).symm, map_zero]
  have heq : castFrame hmc.psi (lact c x) = rmul (lact γ' (castFrame hma.psi (lact a x))) bm := by
    funext τ
    show (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, _⟩ =
      ((γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * ((a : Matrix _ _ _).map τ.1 * mat x ⟨τ.1, _⟩)) *
        (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
    rw [hcm, hs, Matrix.map_mul, Matrix.map_mul]
    have hsc : (Matrix.scalar (Fin D.R.r) s).map τ.1 = Matrix.scalar (Fin D.R.r) (τ.1 s) := by
      ext p q; by_cases hpq : p = q <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hpq]
    rw [hsc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 2
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  have hb := (hU.2.2.2.1 k'' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).2 ⟨γ', hγ', bm, hbm, congrArg (Sigma.mk k'') heq⟩
  obtain ⟨t', ht'⟩ := hb
  exact ⟨hy₁, _, htr _ _ _ _ _ ht' f₂⟩

end GlobalTheory.ShareOn

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAtOfMovesAtOpenSetStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.transporter_movesAt_of_movesAt_open_set : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  first | exact @GlobalTheory.ShareOn.movesAt_of_movesAt_open | exact GlobalTheory.ShareOn.movesAt_of_movesAt_open | (intros; apply GlobalTheory.ShareOn.movesAt_of_movesAt_open <;> assumption)
end
end
