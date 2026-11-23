module

public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.LagrangianStabilizerCharacterTrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DblCoordUnique
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsInvariantForm
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.LagrangianStabilizerCharacterTrivial
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrderStatement
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearActInt
import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlLoc
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearActAlg

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.WeilM

namespace PositivityTheory.ThK.LinAct

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]

omit [Invertible (2 : k)] [DecidableEq α] [DecidableEq β] in
theorem hTens_transpose (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix β α K) :
    hTens c JB JA x y = hTens c JA JB xᵀ yᵀ := by
  unfold hTens
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  simp only [transpose_apply]
  ring

def lagY {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) (Cy : Matrix β ν K) :
    Submodule k ((κ → k) × (κ → k)) :=
  LinearMap.range (d.e.toLinearMap ∘ₗ
    ({ toFun := fun z => Cy * z, map_add' := Matrix.mul_add _, map_smul' := fun r z => Matrix.mul_smul _ r z } :
      Matrix ν α K →ₗ[k] Matrix β α K))

omit [DecidableEq α] [DecidableEq β] [DecidableEq ν] in
theorem mem_lagY {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} {d : Darboux (symp (R := k) c ξ JB JA) κ} {Cy : Matrix β ν K}
    {w : (κ → k) × (κ → k)} : w ∈ lagY d Cy ↔ ∃ z : Matrix ν α K, d.e (Cy * z) = w := by
  simp [lagY, LinearMap.mem_range]

omit [DecidableEq α] [DecidableEq β] [DecidableEq ν] in
theorem lagY_iso {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K} (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K}
    (h : Cyᵀ * JB * Cy.map c = 0) : ∀ w ∈ lagY d Cy, ∀ w' ∈ lagY d Cy, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2 := by
  intro w hw w' hw'
  obtain ⟨z, rfl⟩ := mem_lagY.1 hw
  obtain ⟨z', rfl⟩ := mem_lagY.1 hw'
  have h0 := d.form (Cy * z) (Cy * z')
  have hs : symp (R := k) c ξ JB JA (Cy * z) (Cy * z') = 0 := by
    unfold symp
    rw [hTens_transpose, transpose_mul, transpose_mul,
      GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JA h zᵀ z'ᵀ, mul_zero, map_zero]
  rw [hs] at h0
  exact sub_eq_zero.1 h0.symm

omit [Invertible (2 : k)] in
theorem card_lagr [Nontrivial K] {JB : Matrix β β K} {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Fintype.card β = 2 * Fintype.card ν := by
  obtain ⟨-, Cx, M, -, h1, h2⟩ := h
  let f : (β → K) ≃ₗ[K] (ν ⊕ ν → K) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' (fromCols Cy Cx))
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
  rw [card_eq_of_linearEquiv K f, Fintype.card_sum, two_mul]


omit [Invertible (2 : k)] [Fintype α] [DecidableEq α] in
theorem indep {Cy Cx : Matrix β ν K} {M : Matrix (ν ⊕ ν) β K} (h2 : M * fromCols Cy Cx = 1) {z z' : Matrix ν α K}
    (h : Cy * z + Cx * z' = 0) : z = 0 ∧ z' = 0 := by
  have hrows : fromRows z z' = 0 := by
    calc fromRows z z' = (M * fromCols Cy Cx) * fromRows z z' := by rw [h2, Matrix.one_mul]
      _ = M * (Cy * z + Cx * z') := by rw [Matrix.mul_assoc, fromCols_mul_fromRows]
      _ = 0 := by rw [h, Matrix.mul_zero]
  have e1 := congrArg Matrix.toRows₁ hrows
  have e2 := congrArg Matrix.toRows₂ hrows
  simp only [toRows₁_fromRows, toRows₂_fromRows] at e1 e2
  refine ⟨e1.trans ?_, e2.trans ?_⟩ <;> rfl

omit [DecidableEq α] in
theorem lagY_dim [Nontrivial K] {ξ₀ : K} (hq : IsQuad c ξ₀) {ξ : K} {JA : Matrix α α K} {JB : Matrix β β K}
    (d : Darboux (symp (R := k) c ξ JB JA) κ) {Cy : Matrix β ν K} (h : IsLagr c JB Cy) :
    Module.finrank k (lagY d Cy) = Fintype.card κ := by
  obtain ⟨b, -, -⟩ := hq.basis
  have : Module.Free k K := Module.Free.of_basis b
  have : Module.Finite k K := Module.Finite.of_basis b
  have hK : Module.finrank k K = 2 := by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hcard := card_lagr h
  obtain ⟨-, Cx, M, -, -, hM⟩ := h
  have hd := d.e.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hK, hcard] at hd
  unfold lagY
  rw [LinearMap.finrank_range_of_inj, Module.finrank_matrix, hK]
  · linarith
  · intro z z' hz
    have hz' : Cy * z = Cy * z' := d.e.injective hz
    have h3 : Cy * (z - z') + Cx * (0 : Matrix ν α K) = 0 := by
      rw [Matrix.mul_sub, hz', sub_self, Matrix.mul_zero, add_zero]
    exact sub_eq_zero.1 (indep hM h3).1


omit [Invertible (2 : k)] in
theorem exists_coord {ξ₀ : K} (hq : IsQuad c ξ₀) (ν α : Type) [Fintype ν] [Fintype α] [DecidableEq α] :
    ∃ (r : ℕ) (e : (Fin r → k) ≃ₗ[k] Matrix ν α K), ∀ t : GL α K, ∃ g : GL (Fin r) k,
      (∀ x, e (g.val *ᵥ x) = e x * t.valᵀ) ∧ GeneralLinearGroup.det g =
        Units.map (Algebra.norm k : K →* k) (GeneralLinearGroup.det t) ^ Fintype.card ν := by
  obtain ⟨b, -, -⟩ := hq.basis
  have : Module.Free k K := Module.Free.of_basis b
  have : Module.Finite k K := Module.Finite.of_basis b
  refine ⟨Module.finrank k (Matrix ν α K), (Module.finBasis k (Matrix ν α K)).equivFun.symm, fun t => ?_⟩
  set e := (Module.finBasis k (Matrix ν α K)).equivFun.symm
  let TK : GL α K → Matrix ν α K →ₗ[K] Matrix ν α K := fun s =>
    { toFun := fun x => x * (s : Matrix α α K)ᵀ
      map_add' := fun x y => Matrix.add_mul x y _
      map_smul' := fun a x => Matrix.smul_mul a x _ }
  let F : GL α K → (Fin (Module.finrank k (Matrix ν α K)) → k) →ₗ[k]
      (Fin (Module.finrank k (Matrix ν α K)) → k) := fun s =>
    (e.symm : Matrix ν α K →ₗ[k] _) ∘ₗ (TK s).restrictScalars k ∘ₗ (e.symm.symm : _ →ₗ[k] Matrix ν α K)
  have hF : ∀ s x, F s x = e.symm (e x * (s : Matrix α α K)ᵀ) := fun s x => rfl
  have hinv : ∀ s s' : GL α K, s' * s = 1 → F s' ∘ₗ F s = LinearMap.id := by
    intro s s' hss
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hF, hF, LinearEquiv.apply_symm_apply, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← Units.val_mul, hss, Units.val_one, Matrix.transpose_one, Matrix.mul_one,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply]
  let g : GL (Fin (Module.finrank k (Matrix ν α K))) k :=
    ⟨LinearMap.toMatrix' (F t), LinearMap.toMatrix' (F t⁻¹),
      by rw [← LinearMap.toMatrix'_comp, hinv _ _ (mul_inv_cancel t), LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hinv _ _ (inv_mul_cancel t), LinearMap.toMatrix'_id]⟩
  refine ⟨g, fun x => ?_, ?_⟩
  · change e (LinearMap.toMatrix' (F t) *ᵥ x) = _
    rw [LinearMap.toMatrix'_mulVec, hF, LinearEquiv.apply_symm_apply]
  · have hpi : (Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ TK t ∘ₗ
        (Matrix.ofLinearEquiv K).symm.symm.toLinearMap =
        LinearMap.pi (fun i : ν => (Matrix.toLin' (t : Matrix α α K)).comp (LinearMap.proj i)) := by
      refine LinearMap.ext fun x => funext fun i => funext fun j => ?_
      simp [TK, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    have hdetK : LinearMap.det (TK t) = Matrix.det (t : Matrix α α K) ^ Fintype.card ν := by
      rw [← LinearMap.det_conj (TK t) (Matrix.ofLinearEquiv K).symm, hpi, LinearMap.det_pi,
        Finset.prod_const, Finset.card_univ, LinearMap.det_toLin']
    ext
    change Matrix.det (LinearMap.toMatrix' (F t)) = _
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, hdetK, map_pow]
    simp


omit [DecidableEq α] [DecidableEq β] in
theorem schr_box (ψ : AddChar k ℂ) {κ' : Type} [Fintype κ'] (w : (κ ⊕ κ' → k) × (κ ⊕ κ' → k)) (φ₁ : (κ → k) → ℂ)
    (φ₂ : (κ' → k) → ℂ) : schr ψ w (boxFun φ₁ φ₂) =
      boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁) (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  have hd : ∀ u v : κ ⊕ κ' → k,
      u ⬝ᵥ v = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr) := fun u v => by
    simp [dotProduct, Fintype.sum_sum_type]
  have e1 : (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl := rfl
  have e2 : (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr := rfl
  simp only [schr, boxFun]
  rw [e1, e2, hd x w.2, hd w.1 w.2]
  have e3 : (x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) +
      ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + (w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr)) =
      ((x ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl) + ⅟(2 : k) * ((w.1 ∘ Sum.inl) ⬝ᵥ (w.2 ∘ Sum.inl))) +
      ((x ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr) + ⅟(2 : k) * ((w.1 ∘ Sum.inr) ⬝ᵥ (w.2 ∘ Sum.inr))) := by ring
  rw [e3, AddChar.map_add_eq_mul]
  ring

end PositivityTheory.ThK.LinAct
end
end
end

-- Source module: Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LinearAct

section

@[expose] public section

noncomputable section

open Matrix GlobalTheory.WeilM MeasureTheory PositivityTheory.ThKH.Evl

namespace PositivityTheory.ThK

namespace LinAct

variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {K : Type} [CommRing K] [Nontrivial K] [Algebra k K] {c : K →ₐ[k] K} {ψ : AddChar k ℂ} {ξ₀ ξ : K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  {JA : Matrix α α K} {JB : Matrix β β K} {Cy : Matrix β ν K}

theorem dbl_fix (hc : Continuous ψ) (h1 : ψ ≠ 1) (hq : IsQuad c ξ₀) (hA : IsHerm c JA) (hL : IsLagr c JB Cy)
    (dd : Darboux (symp (R := k) c ξ JB (dbl JA)) κ) (om : UG c (dbl JA) →* Module.End ℂ ((κ → k) → ℂ))
    (hs : IsSplitting (sbClass k) ψ dd (actB c) om) (hr : SiegelRule c (sbClass k) ψ ξ JB (dbl JA) dd 1 (diagCols α) om)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ lagY dd Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) : ∀ g, ∀ φ ∈ SB (κ → k), l (om g φ) = l φ := by
  have hiso := lagY_iso dd hL.1
  have hdim := lagY_dim hq dd hL
  have hcard := card_lagr hL
  have hn := norm_char hc
  have key : ∀ g, ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l (om g φ) = a * l φ := fun g =>
    line hc hn h1 _ hiso hdim l (l ∘ₗ om g) hl (by
      rintro _ ⟨z, rfl⟩ φ hφ
      refine (congrArg l (hs.impl g (Cy * z) φ hφ)).trans (hl _ ?_ _ (hs.pres g φ hφ))
      exact mem_lagY.2 ⟨_, by rw [actB, Matrix.mul_assoc]⟩) hne
  choose a ha using key
  obtain ⟨φ₀, hφ₀, hl₀⟩ := hne
  let A : UG c (dbl JA) →* ℂ :=
    { toFun := a
      map_one' := by
        have := ha 1 φ₀ hφ₀
        rw [map_one, Module.End.one_apply] at this
        exact (mul_eq_right₀ hl₀).1 this.symm
      map_mul' := fun g h => by
        have := ha (g * h) φ₀ hφ₀
        rw [map_mul, Module.End.mul_apply, ha g _ (hs.pres h _ hφ₀), ha h _ hφ₀, ← mul_assoc] at this
        exact (mul_right_cancel₀ hl₀ this).symm }
  obtain ⟨-, Cx, M, -, hM1, hM2⟩ := id hL
  obtain ⟨r, e, he⟩ := exists_coord hq ν α
  have hD := isLagr_diagCols (R := k) c JA
  have hisoD : ∀ z z' : Matrix β α K, (dd.e (z * (diagCols (E := K) α)ᵀ)).1 ⬝ᵥ (dd.e (z' * (diagCols (E := K) α)ᵀ)).2 =
      (dd.e (z' * (diagCols (E := K) α)ᵀ)).1 ⬝ᵥ (dd.e (z * (diagCols (E := K) α)ᵀ)).2 := fun z z' => by
    have h := dd.form (z * (diagCols (E := K) α)ᵀ) (z' * (diagCols (E := K) α)ᵀ)
    rw [symp, GlobalTheory.CompanionTheory.SplitUnique.hTens_eq_zero c JB hD.1, mul_zero, map_zero] at h
    exact sub_eq_zero.mp h.symm
  let X₀ : Matrix ν α K →ₗ[k] Matrix β (α ⊕ α) K :=
    { toFun := fun z => Cx * z * (diagCols (E := K) α)ᵀ
      map_add' := fun z z' => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun t z => by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let X : (Fin r → k) →ₗ[k] (κ → k) × (κ → k) := dd.e.toLinearMap ∘ₗ X₀ ∘ₗ e.toLinearMap
  have hX : ∀ x, X x = dd.e (Cx * e x * (diagCols (E := K) α)ᵀ) := fun _ => rfl
  obtain ⟨L, ⟨φ₁, hφ₁, hL₁⟩, hLX, hLY, hLT⟩ := exists_avg hc h1 _ hiso hdim l hl ⟨φ₀, hφ₀, hl₀⟩ X
    (fun x x' => hisoD _ _) (fun x hx => by
      obtain ⟨z, hz⟩ := mem_lagY.1 hx
      have h2 := dd.e.injective (hz.trans (hX x))
      have h3 := (indep hM2 (z := -z) (z' := e x * (diagCols (E := K) α)ᵀ) (by
        rw [Matrix.mul_neg, h2, Matrix.mul_assoc, neg_add_cancel])).2
      rw [diagCols, transpose_fromRows, transpose_one, mul_fromCols, Matrix.mul_one, ← fromCols_zero] at h3
      exact e.map_eq_zero_iff.1 (fromCols_ext_iff .. |>.1 h3).1)
  have hinv : ∀ z : Matrix β α K, ∀ φ ∈ SB (κ → k), L (dd.rho ψ (z * (diagCols (E := K) α)ᵀ) φ) = L φ := fun z φ hφ => by
    obtain ⟨x, hx⟩ := e.surjective (M * z).toRows₂
    have hz : z = Cy * (M * z).toRows₁ + Cx * e x := by
      rw [hx, ← fromCols_mul_fromRows, fromRows_toRows, ← Matrix.mul_assoc, hM1, Matrix.one_mul]
    rw [Darboux.rho, hz, Matrix.add_mul, map_add (f := _), ← schr_add (hisoD _ _), hLY _ (mem_lagY.2 ⟨_, by rw [Matrix.mul_assoc]⟩)
      (fun x => hisoD _ _) _ (schr_mem hc _ hφ), ← hX, hLX _ _ hφ]
  have hA1 := GlobalTheory.T.lagrangian_stabilizer_character_trivial k K c ξ₀ _ _ _ _ hq (GlobalTheory.CompanionTheory.WeilOneMember.isHerm_dbl hA) hD A.toHomUnits fun p t hp => by
    obtain ⟨g, hg, hdet⟩ := he t
    have e1 := hr L trivial hinv p t hp φ₁ hφ₁
    have e2 := hLT (om p) g (a p) (hs.pres p) (fun x φ hφ => by
      refine (hs.impl p (Cx * e x * (diagCols (E := K) α)ᵀ) φ hφ).trans ?_
      rw [hX, hg, actB, Darboux.rho, Matrix.mul_assoc _ (diagCols (E := K) α)ᵀ, ← transpose_mul, hp, transpose_mul]
      simp only [Matrix.mul_assoc]) (ha p) φ₁ hφ₁
    have e3 := mul_right_cancel₀ hL₁ (e1.symm.trans e2)
    have e4 : (Fintype.card β : ℝ) / 2 = (Fintype.card ν : ℕ) := by rw [hcard]; push_cast; ring
    rw [hdet, map_pow, e4, Real.rpow_natCast, MonoidHom.one_apply, Circle.coe_one, one_mul, NNReal.coe_pow] at e3
    refine Units.ext ((mul_eq_left₀ ?_).1 e3.symm)
    exact_mod_cast pow_ne_zero _ distribHaarChar_pos.ne'
  intro g φ hφ
  have : a g = 1 := congrArg Units.val (DFunLike.congr_fun hA1 g)
  rw [ha g φ hφ, this, one_mul]

theorem weilB_fix (hc : Continuous ψ) (h1 : ψ ≠ 1) (hq : IsQuad c ξ₀) (hA : IsHerm c JA) (hL : IsLagr c JB Cy)
    (d : Darboux (symp (R := k) c ξ JB JA) κ) (om : UG c JA →* Module.End ℂ ((κ → k) → ℂ))
    (hW : IsWeilB c (sbClass k) ψ ξ JB JA d 1 om)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ lagY d Cy, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ)
    (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0) : ∀ g, ∀ φ ∈ SB (κ → k), l (om g φ) = l φ := by
  obtain ⟨hs₀, dd, omd, hdd, hs, hr, hb⟩ := hW
  have hn := norm_char hc
  obtain ⟨l₂, hne₂, hl₂⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form k _ ψ hc h1 _ (lagY_iso dd hL.1)
  have hfix := dbl_fix hc h1 hq hA hL dd omd hs hr l₂ hl₂ hne₂
  obtain ⟨φ₁, h₁, φ₂, h₂, h₁₂⟩ : ∃ φ₁ ∈ SB (κ → k), ∃ φ₂ ∈ SB (κ → k), l₂ (boxFun φ₁ φ₂) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨φ₀, h₀, hl₀⟩ := hne
    obtain ⟨φ, hφ, hφ0⟩ := hne₂
    obtain ⟨y, hy⟩ := Function.ne_iff.mp fun h : φ₀ = 0 => hl₀ (by rw [h, map_zero])
    refine hφ0 (cyc hc hn h1 (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem h₀ h₀) (fun h => ?_) l₂ (fun w => ?_) φ hφ)
    · exact mul_ne_zero hy hy (congrFun h (Sum.elim y y))
    · rw [schr_box]
      exact hcon _ (schr_mem hc _ h₀) _ (schr_mem hc _ h₀)
  let Bx : ((κ → k) → ℂ) →ₗ[ℂ] ((κ ⊕ κ → k) → ℂ) :=
    { toFun := fun φ => boxFun φ φ₂
      map_add' := fun a b => funext fun x => add_mul _ _ _
      map_smul' := fun t a => funext fun x => mul_assoc _ _ _ }
  obtain ⟨a, ha⟩ := line hc hn h1 _ (lagY_iso d hL.1) (lagY_dim hq d hL) l (l₂ ∘ₗ Bx) hl (by
    rintro _ ⟨z, rfl⟩ φ hφ
    have e := hl₂ _ (mem_lagY.2 ⟨fromCols z 0, rfl⟩) _ (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ h₂)
    have e0 : schr ψ (0, 0) φ₂ = φ₂ := by funext x; simp [schr]
    rw [mul_fromCols, hdd, Matrix.mul_zero, map_zero, schr_box] at e
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.fst_zero, Prod.snd_zero, neg_zero, e0] at e
    exact e) hne
  have ha0 : a ≠ 0 := fun h => h₁₂ ((ha φ₁ h₁).trans (by rw [h, zero_mul]))
  intro g φ hφ
  obtain ⟨gd, hgd⟩ := GlobalTheory.CompanionTheory.WeilOneMember.exists_embed g
  have e := hfix gd _ (GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem hφ h₂)
  rw [hb g gd hgd φ hφ φ₂ h₂] at e
  exact mul_left_cancel₀ ha0 ((ha _ (hs₀.pres g φ hφ)).symm.trans (e.trans (ha φ hφ)))

end LinAct

theorem split_character_fixes_evaluation : LinearAct := by
  intro k _ _ _ _ _ _ K _ _ _ _ c ψ hK ⟨ξ₀, hq⟩ hc h1 m n N κ _ JA JB d χ Cy om l hA _ hL ⟨_, d', hd', hW⟩ hev g φ hφ
  have := hK.nontrivial
  refine LinAct.weilB_fix hc h1 hq hA hL d' _ hW l ?_ hev.1 g φ hφ
  rintro _ ⟨z, rfl⟩ φ hφ
  have e := hev.2 zᵀ φ hφ
  rw [Darboux.rho, ← hd', transpose_mul, transpose_transpose, transpose_transpose] at e
  exact e

end PositivityTheory.ThK
end
end
end
