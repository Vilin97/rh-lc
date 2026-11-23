module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.CartanPos
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC
public import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
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
import Mathlib.RingTheory.TotallySplit
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsGaussBox

section

@[expose] public section

noncomputable section

open scoped SchwartzMap

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt Lib

variable {A κ κ₀ κ₁ : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [Fintype κ] [Fintype κ₀] [Fintype κ₁] (ε : κ ≃ κ₀ ⊕ κ₁)

theorem hcongr {f g : ℝ → ℂ} {a b : ℂ} {x : ℝ} (h : HasDerivAt f a x) (hf : ∀ t, g t = f t) (ha : b = a) : HasDerivAt g b x := by
  rw [ha, funext hf]; exact h

theorem hd {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) (x v : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f (x + s • v) v) s := by
  have h := (f.hasFDerivAt (x + s • v)).comp_hasDerivAt s (((hasDerivAt_id s).smul_const v).const_add x)
  rw [one_smul] at h
  exact h

theorem hd0 {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : 𝓢(V, ℂ)) (x v : V) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  simpa using hd f x v 0

theorem dop_smul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (c : ℂ) (f : 𝓢(V, ℂ)) :
    dop a L (c • f) = c • dop a L f := by
  ext x
  have h1 := op_apply a L (c • f) x
  have h2 := op_apply a L f x
  rw [LineDeriv.lineDerivOp_smul] at h1
  change op a L (c • f) x = c * op a L f x
  rw [h1, h2]
  change c * _ + _ * (_ * (c * _)) = _
  ring

theorem dop_add' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f g : 𝓢(V, ℂ)) :
    dop a L (f + g) = dop a L f + dop a L g := by
  simp only [dop, LineDeriv.lineDerivOp_add, map_add (f := _), smul_add]
  abel

theorem dop_neg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    dop (-a) (-L) f = -dop a L f := by
  ext x
  simp only [SchwartzMap.neg_apply, dop_apply, map_neg, ContinuousLinearMap.neg_apply]
  push_cast
  ring

omit [Fintype κ₀] in
theorem slice_dop (f : 𝓢(κ → A, ℂ)) (g : 𝓢(κ₁ → A, ℂ)) (a : κ₀ → A) (h : ∀ y, g y = f (glue ε a y)) (L : (κ → A) →L[ℝ] ℝ)
    (L₁ : (κ₁ → A) →L[ℝ] ℝ) (hL : ∀ y, L (glue ε a y) = L₁ y) (v y : κ₁ → A) :
    dop (glue ε 0 v) L f (glue ε a y) = dop v L₁ g y := by
  rw [dop_apply, dop_apply, hL, h]
  congr 1
  refine (hd0 f _ _).unique ?_
  refine hcongr (hd0 g y v) (fun t => ?_) rfl
  rw [h, glue_smul, glue_add, smul_zero, add_zero]

omit [Fintype κ₀] [Fintype κ₁] in
theorem slice_normal (f : 𝓢(κ → A, ℂ)) (h : (κ₁ → A) → ℂ) (hf : ∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * h y) (p a : κ₀ → A) :
    ∃ c : ℂ, ∀ y, fderiv ℝ f (glue ε a y) (glue ε p 0) = c * h y := by
  have e : ∀ y (t : ℝ), glue ε a y + t • glue ε p 0 = glue ε (a + t • p) y := fun y t => by
    rw [glue_smul, glue_add, smul_zero, add_zero]
  by_cases h0 : h = 0
  · refine ⟨0, fun y => (hd0 f _ _).unique ?_⟩
    refine hcongr (hasDerivAt_const (0 : ℝ) (0 : ℂ)) (fun t => ?_) ?_
    · obtain ⟨c, hc⟩ := hf (a + t • p)
      rw [e, hc, h0]; simp
    · simp
  · obtain ⟨y₀, hy⟩ := Function.ne_iff.1 h0
    refine ⟨fderiv ℝ f (glue ε a y₀) (glue ε p 0) / h y₀, fun y => (hd0 f _ _).unique ?_⟩
    refine hcongr (((hd0 f (glue ε a y₀) (glue ε p 0)).div_const (h y₀)).mul_const (h y)) (fun t => ?_) rfl
    obtain ⟨c, hc⟩ := hf (a + t • p)
    rw [e, e, hc, hc, mul_div_cancel_right₀ _ hy]

omit [Fintype κ₀] [Fintype κ₁] in
theorem slice_ode (f : 𝓢(κ → A, ℂ)) (a : κ₀ → A) (l : ℝ)
    (h : ∀ (t : ℝ) y, fderiv ℝ f (glue ε (t • a) y) (glue ε a 0) = -(2 * t * l) * f (glue ε (t • a) y)) (y : κ₁ → A) :
    f (glue ε a y) = Complex.exp (-l) * f (glue ε 0 y) := by
  have e : ∀ t : ℝ, glue ε 0 y + t • glue ε a 0 = glue ε (t • a) y := fun t => by
    rw [glue_smul, glue_add, smul_zero, add_zero, zero_add]
  have h1 : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) ^ 2 * l) * f (glue ε 0 y + t • glue ε a 0)) 0 s := fun s => by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * l) (2 * s * l) s := by
      simpa using (((hasDerivAt_pow 2 (s : ℂ)).comp_ofReal).mul_const (l : ℂ))
    refine hcongr (h2.cexp.fun_mul (hd f (glue ε 0 y) (glue ε a 0) s)) (fun _ => rfl) ?_
    rw [e, h]
    ring
  have h3 := is_const_of_deriv_eq_zero (fun s => (h1 s).differentiableAt) (fun s => (h1 s).deriv) 1 0
  simp only [e] at h3
  simp only [one_smul, zero_smul, Complex.ofReal_one, one_pow, one_mul, Complex.ofReal_zero] at h3
  rw [Complex.exp_neg, eq_inv_mul_iff_mul_eq₀ (Complex.exp_ne_zero _), h3]
  simp

theorem exists_gauss_box [FiniteDimensional ℝ A] (Q : (κ₀ → A) →ₗ[ℝ] (κ₀ → A) →ₗ[ℝ] ℝ) (hs : ∀ a b, Q a b = Q b a)
    (hp : ∀ a, a ≠ 0 → 0 < Q a a) (g : 𝓢(κ₁ → A, ℂ)) : ∃ f : 𝓢(κ → A, ℂ), (∀ y, f (glue ε 0 y) = g y) ∧
      (∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * g y) ∧
      ∀ a y p, fderiv ℝ f (glue ε a y) (glue ε p 0) = -(2 * Real.pi * Q a p) * f (glue ε a y) := by
  let Qc : (κ₀ → A) →L[ℝ] (κ₀ → A) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((κ₀ → A) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ ((-Real.pi) • Q))
  have hQ : ∀ a b, Qc a b = -Real.pi * Q a b := fun _ _ => rfl
  obtain ⟨G, hG⟩ := exists_schwartz_exp_diag Qc fun a ha => by
    rw [hQ]; exact mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) (hp a ha)
  let f := schwartzBox G g (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε.symm (.inl i)))
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε.symm (.inr i))) fun x : κ → A => by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
      obtain ⟨k, rfl⟩ := ε.symm.surjective k
      rcases k with k | k
      · exact le_max_of_le_left (norm_le_pi_norm (fun i => x (ε.symm (.inl i))) k)
      · exact le_max_of_le_right (norm_le_pi_norm (fun i => x (ε.symm (.inr i))) k)
  have hf : ∀ a y, f (glue ε a y) = Complex.exp (-Real.pi * Q a a) * g y := fun a y => by
    show G (fun i => glue ε a y _) * g (fun i => glue ε a y _) = _
    simp only [glue_inl, glue_inr, hG, hQ]
    push_cast
    rfl
  refine ⟨f, fun y => by simp [hf], fun a => ⟨_, hf a⟩, fun a y p => (hd0 f _ _).unique ?_⟩
  have h2 : HasDerivAt (fun t : ℝ => -(Real.pi : ℂ) * (Q a a + 2 * t * Q a p + (t : ℂ) ^ 2 * Q p p))
      (-(Real.pi : ℂ) * (2 * (Q a p : ℂ))) 0 :=
    hcongr ((((((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul 2).mul_const (Q a p : ℂ)).const_add (Q a a : ℂ)).fun_add
      ((hasDerivAt_pow 2 ((0 : ℝ) : ℂ)).mul_const (Q p p : ℂ))).const_mul (-(Real.pi : ℂ))).comp_ofReal (fun _ => rfl) (by simp)
  refine hcongr (h2.cexp.mul_const (g y)) (fun t => ?_) ?_
  · skip
    rw [glue_smul, glue_add, smul_zero, add_zero, hf]
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hs p a]
    push_cast
    congr 2
    ring
  · rw [hf]
    simp
    ring

end PositivityTheory.ThKF0
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsRelationAdaptedVector

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt Lib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ r s r' s' i₀ i₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {B : Base F E} {H : Plane E d d₁}

def Dp (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) : SInf F (Fin n × Fin d) :=
  dop (aOf M u) (lOf M u) f

def Gs (B : Base F E) (M : Model σ X W) (e : InfinitePlace F → ℤˣ) (f : SInf F (Fin n × Fin d)) : Prop :=
  ∀ u u', At (evI F) u → At (evI F) u' → Rel B X W e u u' → Dp M u' f = Complex.I • Dp M u f

theorem gauss_iff (hB : B.IsGood σ) (M : Model σ X W) (f) : M.IsGauss B.ψ B.emb f ↔ ∃ e, Gs B M e f :=
  exists_congr fun _ => forall₂_congr fun _ _ => forall₃_congr fun hu hu' _ =>
    ⟨fun h => h _ _ (actsD_dop M hB.std hu f) (actsD_dop M hB.std hu' f), fun h _ _ hg hg' => by
      rw [actsD_unique M hB.std hu hg, actsD_unique M hB.std hu' hg']; exact h⟩

theorem pol_gs (hB : B.IsGood σ) {M : Model σ X W} {e f} (h : Gs B M e f) : f ∈ M.Pol B.ψ B.emb :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f ((gauss_iff hB M f).2 ⟨e, h⟩)

theorem pol_Dp (hB : B.IsGood σ) {M : Model σ X W} {u f} (hu : At (evI F) u) (h : f ∈ M.Pol B.ψ B.emb) :
    Dp M u f ∈ M.Pol B.ψ B.emb :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 h N hN) _ (actsD_dop M hB.std hu f)

theorem pol_le (hB : B.IsGood σ) {M : Model σ X W} {N : Submodule ℂ (SInf F (Fin n × Fin d))} (h1 : ∀ e f, Gs B M e f → f ∈ N)
    (h2 : ∀ u, At (evI F) u → ∀ f ∈ N, Dp M u f ∈ N) : M.Pol B.ψ B.emb ≤ N :=
  sInf_le ⟨fun f hf => by obtain ⟨e, he⟩ := (gauss_iff hB M f).1 hf; exact h1 e f he,
    fun u hu f hf _ h => by rw [actsD_unique M hB.std hu h]; exact h2 u hu f hf⟩

theorem Dp_add (M : Model σ X W) (u u' f) : Dp M (u + u') f = Dp M u f + Dp M u' f := by
  rw [Dp, aOf_add, lOf_add, dop_add]; rfl

theorem aOf_zero (M : Model σ X W) : aOf M 0 = 0 := by
  have := aOf_add M 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem aOf_neg (M : Model σ X W) (u) : aOf M (-u) = -aOf M u :=
  eq_neg_of_add_eq_zero_left (by rw [← aOf_add, neg_add_cancel, aOf_zero])

theorem lOf_neg (M : Model σ X W) (u) : lOf M (-u) = -lOf M u := by
  have := lOf_add M 0 0
  rw [add_zero] at this
  exact eq_neg_of_add_eq_zero_left (by rw [← lOf_add, neg_add_cancel, left_eq_add.1 this])

theorem omega_co (M : Model σ X W) (u u') : omega σ X W u u' = lOf M u' (aOf M u) - lOf M u (aOf M u') := by
  rw [omega, M.co.form u u', evI_sub, map_sub]
  simp only [lOf, aOf, linForm_apply, dotProduct, evI_sum, evI_mul]

theorem lin_glue {κ κ₀ κ₁ : Type} [Fintype κ] [Fintype κ₀] [Fintype κ₁] (ε : κ ≃ κ₀ ⊕ κ₁) (q a : κ₀ → mixedEmbedding.mixedSpace F)
    (c y : κ₁ → mixedEmbedding.mixedSpace F) : linForm (glue ε q c) (glue ε a y) = linForm q a + linForm c y := by
  rw [linForm_apply, linForm_apply, linForm_apply, ← map_add (f := _)]
  exact congrArg _ (glue_dot ε a q y c)

theorem lin_zero {κ : Type} [Fintype κ] : linForm (0 : κ → mixedEmbedding.mixedSpace F) = 0 := by
  ext y; simp [linForm_apply]

theorem evI_fun_zero {κ : Type} : (fun k : κ => evI F ((0 : κ → AF F) k)) = 0 := funext fun _ => evI_zero

theorem map_pure (w : InfinitePlace F) (a : Fin n → AE F E) (b : Fin d → E) :
    (Matrix.vecMulVec a (incV F b)).map (piInf (B.emb w)) =
      Matrix.vecMulVec (fun i => piInf (B.emb w) (a i)) fun i => (B.emb w).1 (b i) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV]
  simp [piInf, inclR, compInf, infEmb]

theorem at_pure {a : Fin n → AE F E} (ha : At (evI F) a) (b : Fin d → AE F E) : At (evI F) (Matrix.vecMulVec a b) := fun t ht => by
  rw [← Matrix.smul_vecMulVec, ha t ht, Matrix.zero_vecMulVec]

theorem at_mul' {α β γ : Type} [Fintype β] {u : Matrix α β (AE F E)} (hu : At (evI F) u) (N : Matrix β γ (AE F E)) :
    At (evI F) (u * N) := fun t ht => by rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]

theorem decomp (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    ∃ (a : Fin n → AE F E) (z : Matrix (Fin n) (Fin d₁) (AE F E)) (b : Fin n → AE F E), At (evI F) a ∧ At (evI F) z ∧ At (evI F) b ∧
      u = Matrix.vecMulVec a (incV F H.x) + z * (incM F H.ι)ᵀ + Matrix.vecMulVec b (incV F H.y) := by
  obtain ⟨Q, h1, -, -⟩ := exists_frame_inv hH hW.lat
  have hw := at_mul' hu (incM F Q)ᵀ
  have e : u = u * (incM F Q)ᵀ * (incM F (frame H))ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← incM_mul, h1, incM, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one, Matrix.mul_one]
  generalize u * (incM F Q)ᵀ = w at hw e
  refine ⟨fun i => w i (.inr 0), w.submatrix id .inl, fun i => w i (.inr 1),
    fun t ht => funext fun i => congrFun (congrFun (hw t ht) i) _,
    fun t ht => Matrix.ext fun i j => congrFun (congrFun (hw t ht) i) _,
    fun t ht => funext fun i => congrFun (congrFun (hw t ht) i) _, ?_⟩
  rw [e]
  ext i j
  simp [frame, incM, incV, Matrix.mul_apply, Matrix.vecMulVec_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem rel_iota (hH : H.IsAdapted σ B W W₁ i₀ i₁) {e} {z z' : Matrix (Fin n) (Fin d₁) (AE F E)} (h : Rel B X W₁ e z z') :
    Rel B X W e (z * (incM F H.ι)ᵀ) (z' * (incM F H.ι)ᵀ) := fun w => by
  have h1 : ((incM F H.ι)ᵀ).map (piInf (B.emb w)) = (H.ι.map (B.emb w).1)ᵀ := by
    ext i j; simp [incM, piInf, inclR, compInf, infEmb]
  have h2 := congrArg Matrix.transpose (hH.cartan w).1
  rw [Matrix.transpose_mul, Matrix.transpose_mul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, h1, h w, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, h2]

theorem rel_pure (hB : B.IsGood σ) (e) {x y : Fin d → E} (c : InfinitePlace F → ℂ)
    (h : ∀ w, W.θ w *ᵥ (fun i => (B.emb w).1 (x i)) = c w • fun i => (B.emb w).1 (y i)) (a : Fin n → AE F E) :
    ∃ b, At (evI F) b ∧ Rel B X W e (Matrix.vecMulVec a (incV F x)) (Matrix.vecMulVec b (incV F y)) := by
  obtain ⟨b, h1, h2⟩ := exists_vec hB fun w => (((e w : ℤ) : ℂ) * Complex.I * c w) • X.θ w *ᵥ fun i => piInf (B.emb w) (a i)
  refine ⟨b, h1, fun w => ?_⟩
  rw [map_pure, map_pure, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, h w]
  ext i j
  simp only [h2, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem rel_y (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) (e) (b : Fin n → AE F E) :
    ∃ a, At (evI F) a ∧ Rel B X W e (Matrix.vecMulVec b (incV F H.y)) (Matrix.vecMulVec a (incV F H.x)) := by
  choose c _ hc using fun w => (hH.cartan w).2
  exact rel_pure hB e c (fun w => by rw [hc w, Matrix.mulVec_smul, Matrix.mulVec_mulVec, (hW.cartan w).1, Matrix.one_mulVec]) b

theorem exists_relation_adapted_vector (hB : B.IsGood σ) (hH : H.IsAdapted σ B W W₁ i₀ i₁) (e) (a : Fin n → AE F E) :
    ∃ b, At (evI F) b ∧ Rel B X W e (Matrix.vecMulVec a (incV F H.x)) (Matrix.vecMulVec b (incV F H.y)) := by
  choose c h0 hc using fun w => (hH.cartan w).2
  exact rel_pure hB e (fun w => (c w)⁻¹) (fun w => by rw [hc w, inv_smul_smul₀ (h0 w)]) a

variable {κ₀ : Type} [Fintype κ₀] {ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n × Fin d₁} {Ma : Model σ X W} {M₁ : Model σ X W₁}

structure Adp (H : Plane E d d₁) (ε : Fin n × Fin d ≃ κ₀ ⊕ Fin n × Fin d₁) (Ma : Model σ X W) (M₁ : Model σ X W₁) : Prop where
  i : ∀ z : Matrix (Fin n) (Fin d₁) (AE F E), Ma.co.e (z * (incM F H.ι)ᵀ) = (glue ε 0 (M₁.co.e z).1, glue ε 0 (M₁.co.e z).2)
  x : ∀ y, ∃ q, Ma.co.e (Matrix.vecMulVec y (incV F H.x)) = (0, glue ε q 0)
  y : ∀ y, ∃ p, Ma.co.e (Matrix.vecMulVec y (incV F H.y)) = (glue ε p 0, 0)

namespace Adp

variable (h : Adp H ε Ma M₁)
include h

theorem ai (z : Matrix (Fin n) (Fin d₁) (AE F E)) : aOf Ma (z * (incM F H.ι)ᵀ) = glue ε 0 (aOf M₁ z) := by
  unfold aOf
  rw [h.i, glue_map ε (evI F), evI_fun_zero]

theorem li (z : Matrix (Fin n) (Fin d₁) (AE F E)) (a y) : lOf Ma (z * (incM F H.ι)ᵀ) (glue ε a y) = lOf M₁ z y := by
  unfold lOf
  rw [h.i, glue_map ε (evI F), evI_fun_zero, lin_glue, lin_zero, ContinuousLinearMap.zero_apply, zero_add]

theorem cx (a) : ∃ q, aOf Ma (Matrix.vecMulVec a (incV F H.x)) = 0 ∧
    ∀ t y, lOf Ma (Matrix.vecMulVec a (incV F H.x)) (glue ε t y) = linForm q t := by
  obtain ⟨q, hq⟩ := h.x a
  refine ⟨fun k => evI F (q k), ?_, fun t y => ?_⟩
  · unfold aOf
    rw [hq, evI_fun_zero]
  · unfold lOf
    rw [hq, glue_map ε (evI F), evI_fun_zero, lin_glue, lin_zero, ContinuousLinearMap.zero_apply, add_zero]

theorem cy (b) : ∃ p, aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε p 0 ∧ lOf Ma (Matrix.vecMulVec b (incV F H.y)) = 0 := by
  obtain ⟨p, hp⟩ := h.y b
  refine ⟨fun k => evI F (p k), ?_, ?_⟩
  · unfold aOf
    rw [hp, glue_map ε (evI F), evI_fun_zero]
  · unfold lOf
    rw [hp, evI_fun_zero, lin_zero]

theorem slice {f g a} (hg : ∀ y, g y = f (glue ε a y)) (z : Matrix (Fin n) (Fin d₁) (AE F E)) (y) : Dp Ma (z * (incM F H.ι)ᵀ) f (glue ε a y) = Dp M₁ z g y := by
  rw [Dp, h.ai]
  exact slice_dop ε f g a hg _ _ (h.li z a) _ y

theorem onto (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : κ₀ → mixedEmbedding.mixedSpace F) :
    ∃ b, At (evI F) b ∧ aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε t 0 := by
  have h0 : At (evI F) (Ma.co.e.symm (glue ε (pt t 0) 0, 0)) := fun c hc => by
    have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hc.trans (map_zero _).symm)
    have h2 : c • pt t 0 = 0 := funext fun k => Prod.ext (by change c.1 * _ = 0; rw [h1, zero_mul]) (by change c.2 * 0 = 0; rw [mul_zero])
    rw [← map_smul, Prod.smul_mk, glue_smul, h2, smul_zero, smul_zero, glue_zero, Prod.mk_zero_zero, map_zero]
  obtain ⟨a, z, b, -, -, hb, e⟩ := decomp hW hH h0
  have h1 := congrArg (aOf Ma) e
  obtain ⟨q, hq, -⟩ := h.cx a
  obtain ⟨p, hp, -⟩ := h.cy b
  rw [aOf_add, aOf_add, hq, h.ai, hp, zero_add, glue_add, zero_add] at h1
  refine ⟨b, hb, hp.trans ?_⟩
  congr 1
  funext k
  have := congrFun h1 (ε.symm (.inl k))
  rw [glue_inl, aOf, LinearEquiv.apply_symm_apply] at this
  simp only [glue_inl] at this
  rw [← this]
  exact congrFun (evI_pt t 0) k

theorem gs_slice (hH : H.IsAdapted σ B W W₁ i₀ i₁) {e f g} (hf : Gs B Ma e f) (hg : ∀ y, g y = f (glue ε 0 y)) : Gs B M₁ e g :=
  fun z z' hz hz' hr => by
    ext y
    rw [SchwartzMap.smul_apply, ← h.slice hg, ← h.slice hg, hf _ _ (at_mul' hz _) (at_mul' hz' _) (rel_iota hH hr)]
    rfl

theorem map_le (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) (hT : ∀ f y, T f y = f (glue ε 0 y)) :
    (Ma.Pol B.ψ B.emb).map T ≤ M₁.Pol B.ψ B.emb := by
  let S : Set (SInf F (Fin n × Fin d)) := {f | ∃ g ∈ M₁.Pol B.ψ B.emb, ∀ a, ∃ c : ℂ, ∀ y, f (glue ε a y) = c * g y}
  have h1 : Ma.Pol B.ψ B.emb ≤ Submodule.span ℂ S := by
    refine pol_le hB (fun e f hf => Submodule.subset_span ⟨T f, pol_gs hB (h.gs_slice hH hf (hT f)), fun t => ?_⟩) fun u hu f hf => ?_
    · obtain ⟨b, hb, hp⟩ := h.onto hW hH t
      obtain ⟨-, -, hl⟩ := h.cy b
      obtain ⟨a, ha, hr⟩ := rel_y (X := X) hB hW hH e b
      obtain ⟨q, hq, hq'⟩ := h.cx a
      have key := hf _ _ (at_pure hb _) (at_pure ha _) hr
      refine ⟨_, fun y => (slice_ode ε f t (Real.pi * linForm q t) (fun c y => ?_) y).trans (by rw [hT])⟩
      have := DFunLike.congr_fun key (glue ε (c • t) y)
      simp only [Dp, SchwartzMap.smul_apply, dop_apply, hq, hq', hp, hl, map_zero, map_smul, ContinuousLinearMap.zero_apply,
        smul_eq_mul] at this
      push_cast at this ⊢
      linear_combination Complex.I * this + (fderiv ℝ f (glue ε (c • t) y) (glue ε t 0) +
        2 * Real.pi * c * linForm q t * f (glue ε (c • t) y)) * Complex.I_mul_I
    · induction hf using Submodule.span_induction with
      | zero => rw [← zero_smul ℂ (0 : SInf F _), Dp, dop_smul, zero_smul]; exact zero_mem _
      | add f g _ _ hf hg => rw [Dp, dop_add']; exact add_mem hf hg
      | smul c f _ hf => rw [Dp, dop_smul]; exact Submodule.smul_mem _ c hf
      | mem f hf =>
        obtain ⟨g, hg, hc⟩ := hf
        obtain ⟨a, z, b, -, hz, -, rfl⟩ := decomp hW hH hu
        rw [Dp_add, Dp_add]
        refine add_mem (add_mem (Submodule.subset_span ⟨g, hg, fun t => ?_⟩)
          (Submodule.subset_span ⟨_, pol_Dp hB hz hg, fun t => ?_⟩)) (Submodule.subset_span ⟨g, hg, fun t => ?_⟩)
        · obtain ⟨q, hq, hq'⟩ := h.cx a
          obtain ⟨c, hc⟩ := hc t
          refine ⟨-(2 * Real.pi * Complex.I) * linForm q t * c, fun y => ?_⟩
          rw [Dp, dop_apply, hq, hq', map_zero, hc]
          ring
        · obtain ⟨c, hc⟩ := hc t
          refine ⟨c, fun y => ?_⟩
          rw [h.slice (g := c • g) (fun y => (hc y).symm), Dp, dop_smul]
          rfl
        · obtain ⟨p, hp, hl⟩ := h.cy b
          obtain ⟨c, hc⟩ := slice_normal ε f g hc p t
          refine ⟨c, fun y => ?_⟩
          rw [Dp, dop_apply, hp, hl, hc]
          simp
  refine (Submodule.map_mono h1).trans ?_
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, ⟨g, hg, hc⟩, rfl⟩
  obtain ⟨c, hc⟩ := hc 0
  rw [show T f = c • g from SchwartzMap.ext fun y => (hT f y).trans (hc y)]
  exact Submodule.smul_mem _ c hg

theorem gs_one (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) {e g}
    (hg : Gs B M₁ e g) (h0 : g ≠ 0) : Gs B M₁ 1 g := by
  by_cases hne : Nonempty (Fin n × Fin d₁)
  swap
  · exact fun z z' hz hz' _ => hg z z' hz hz' fun w => Matrix.ext fun i j => (hne ⟨(i, j)⟩).elim
  obtain ⟨i, j⟩ := hne
  suffices e = 1 from this ▸ hg
  funext w₀
  by_contra hw
  have hw' : e w₀ = -1 := (Int.units_eq_one_or _).resolve_left hw
  obtain ⟨a, ha, ha'⟩ := exists_vec hB fun w (_ : Fin n) => if w = w₀ then 1 else 0
  obtain ⟨z', hz', hr⟩ := exists_rel hB X W₁ e (Matrix.vecMulVec a (incV F (Pi.single j 1)))
  have hr' := rel_iota hH hr
  have e1 : Matrix.vecMulVec a (incV F (Pi.single j 1)) * (incM F H.ι)ᵀ = Matrix.vecMulVec a (incV F (H.ι *ᵥ Pi.single j 1)) := by
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    congr 1
    exact funext fun i => (RingHom.map_mulVec (inclR (F := F) (AF F)) H.ι _ i).symm
  have hb : H.ι *ᵥ Pi.single j 1 ≠ 0 := fun hb => by
    obtain ⟨Q, -, h2, -⟩ := exists_frame_inv hH hW.lat
    have h3 := frame_mulVec H (Sum.elim (Pi.single j 1) 0)
    simp only [Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_smul, hb, add_zero] at h3
    have h4 := congrArg (Q *ᵥ ·) h3
    simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at h4
    simpa using congrFun h4 (.inl j)
  have h5 := omega_co Ma (Matrix.vecMulVec a (incV F (Pi.single j 1)) * (incM F H.ι)ᵀ) (z' * (incM F H.ι)ᵀ)
  rw [h.ai, h.ai, h.li, h.li, e1] at h5
  rw [e1] at hr'
  obtain ⟨p, hp, hp'⟩ := omega_pure hB hX hW a hb hr'
  refine h0 (eq_zero_of_neg g _ _ _ _ (hg _ _ (at_pure ha _) hz' hr) ?_)
  rw [← h5, hp, Finset.sum_eq_single w₀ (fun w _ hw => by rw [(hp' w).1 (funext fun k => by simp [ha', hw]), mul_zero]) (by simp), hw']
  have := (hp' w₀).2 fun h0 => by simpa [ha'] using congrFun h0 i
  simpa using this

theorem exists_lift (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁) {g}
    (hg : Gs B M₁ 1 g) : ∃ f, Gs B Ma 1 f ∧ ∀ y, f (glue ε 0 y) = g y := by
  have sym : ∀ {b a b' a' p p' q q'}, Rel B X W 1 (Matrix.vecMulVec b (incV F H.y)) (Matrix.vecMulVec a (incV F H.x)) →
      Rel B X W 1 (Matrix.vecMulVec b' (incV F H.y)) (Matrix.vecMulVec a' (incV F H.x)) →
      aOf Ma (Matrix.vecMulVec b (incV F H.y)) = glue ε p 0 → aOf Ma (Matrix.vecMulVec b' (incV F H.y)) = glue ε p' 0 →
      (∀ t y, lOf Ma (Matrix.vecMulVec a (incV F H.x)) (glue ε t y) = linForm q t) →
      (∀ t y, lOf Ma (Matrix.vecMulVec a' (incV F H.x)) (glue ε t y) = linForm q' t) → linForm q' p = linForm q p' := by
    intro b a b' a' p p' q q' h1 h2 h3 h4 h5 h6
    have := omega_rel hB hX hW h2 (h1.symm hX hW)
    rw [omega_co Ma, omega_co Ma, aOf_neg, lOf_neg, (h.cy b).choose_spec.2, (h.cy b').choose_spec.2, map_neg, h3, h4, h5, h6] at this
    simpa using this
  choose b hb hp using h.onto hW hH
  choose a ha hr using fun t => rel_y (X := X) hB hW hH 1 (b t)
  choose q hq hq' using fun t => h.cx (a t)
  have hs : ∀ t t', linForm (q t') t = linForm (q t) t' := fun t t' => sym (hr t) (hr t') (hp t) (hp t') (hq' t) (hq' t')
  let Q : (κ₀ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ₀ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun t t' => linForm (q t') t) (fun _ _ _ => map_add _ _ _) (fun _ _ _ => map_smul _ _ _)
      (fun t _ _ => by rw [hs, map_add (f := _), hs _ t, hs _ t]) fun c t _ => by rw [hs, map_smul, hs _ t]
  have hy : H.y ≠ 0 := fun h0 => by simpa [h0, form, dotProduct, Matrix.mulVec] using hH.xy
  obtain ⟨f, f0, f1, f2⟩ := exists_gauss_box ε Q hs (fun t ht => by
    obtain ⟨p, h1, h2⟩ := omega_pure hB hX hW (b t) hy (hr t)
    rw [omega_co Ma, hp, hq', (h.cy _).choose_spec.2, ContinuousLinearMap.zero_apply, sub_zero] at h1
    have h3 : ∃ w, (fun i => piInf (B.emb w) (b t i)) ≠ 0 := by
      by_contra! h4
      have h5 : b t = 0 := funext fun i => GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hB.cm B.emb _
        (fun c hc => congrFun (hb t c hc) i) fun w => congrFun (h4 w) i
      have h6 := hp t
      rw [h5, Matrix.zero_vecMulVec, aOf_zero] at h6
      exact ht (funext fun k => by simpa using (congrFun h6 (ε.symm (.inl k))).symm)
    obtain ⟨w, hw⟩ := h3
    refine lt_of_lt_of_eq (Finset.sum_pos' (fun w _ => ?_) ⟨w, Finset.mem_univ _, by simpa using (h2 w).2 hw⟩) h1.symm
    by_cases h4 : (fun i => piInf (B.emb w) (b t i)) = 0
    · simp [(h2 w).1 h4]
    · simpa using ((h2 w).2 h4).le) g
  have K : ∀ b' a', Rel B X W 1 (Matrix.vecMulVec b' (incV F H.y)) (Matrix.vecMulVec a' (incV F H.x)) →
      Dp Ma (Matrix.vecMulVec a' (incV F H.x)) f = Complex.I • Dp Ma (Matrix.vecMulVec b' (incV F H.y)) f := fun b' a' h1 => by
    obtain ⟨p', h2, h3⟩ := h.cy b'
    obtain ⟨q', h4, h5⟩ := h.cx a'
    ext x
    obtain ⟨t, y, rfl⟩ := exists_glue ε x
    have h6 : linForm q' t = Q t p' := (sym (hr t) h1 (hp t) h2 (hq' t) h5).trans (hs p' t)
    simp only [Dp, SchwartzMap.smul_apply, dop_apply, h2, h3, h4, h5, h6, f2, map_zero, ContinuousLinearMap.zero_apply, smul_eq_mul]
    push_cast
    ring
  refine ⟨f, fun u u' hu hu' hrel => ?_, f0⟩
  obtain ⟨a₁, z, b₁, ha₁, hz, hb₁, rfl⟩ := decomp hW hH hu
  obtain ⟨b₂, hb₂, r1⟩ := exists_relation_adapted_vector (X := X) hB hH 1 a₁
  obtain ⟨z', hz', r2⟩ := exists_rel hB X W₁ 1 z
  obtain ⟨a₂, ha₂, r3⟩ := rel_y (X := X) hB hW hH 1 b₁
  rw [hrel.unique hB ((r1.add (rel_iota hH r2)).add r3) hu' fun c hc => by
    rw [smul_add, smul_add, at_pure hb₂ _ c hc, at_mul' hz' _ c hc, at_pure ha₂ _ c hc, add_zero, add_zero]]
  have k1 := K b₂ (-a₁) (by rw [Matrix.neg_vecMulVec]; exact r1.symm hX hW)
  rw [Matrix.neg_vecMulVec, Dp, aOf_neg, lOf_neg, dop_neg, neg_eq_iff_eq_neg] at k1
  have k2 : Dp Ma (z' * (incM F H.ι)ᵀ) f = Complex.I • Dp Ma (z * (incM F H.ι)ᵀ) f := by
    ext x
    obtain ⟨t, y, rfl⟩ := exists_glue ε x
    obtain ⟨c, hc⟩ := f1 t
    have h1 := DFunLike.congr_fun (hg z z' hz hz' r2) y
    rw [SchwartzMap.smul_apply, h.slice (g := c • g) (fun y => (hc y).symm), h.slice (g := c • g) (fun y => (hc y).symm), Dp, Dp,
      dop_smul, dop_smul, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_comm]
    exact congrArg _ h1
  rw [Dp_add, Dp_add, Dp_add, Dp_add, K _ _ r3, k2, smul_add, smul_add]
  congr 2
  change _ = Complex.I • dop _ _ f
  rw [k1, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]

theorem map_eq (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hH : H.IsAdapted σ B W W₁ i₀ i₁)
    (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) (hT : ∀ f y, T f y = f (glue ε 0 y)) :
    (Ma.Pol B.ψ B.emb).map T = M₁.Pol B.ψ B.emb := by
  refine le_antisymm (h.map_le hB hW hH T hT) (pol_le hB (fun e g hg => ?_) ?_)
  · by_cases h0 : g = 0
    · exact h0 ▸ zero_mem _
    obtain ⟨f, hf, hf'⟩ := h.exists_lift hB hX hW hH (h.gs_one hB hX hW hH hg h0)
    exact ⟨f, pol_gs hB hf, SchwartzMap.ext fun y => (hT f y).trans (hf' y)⟩
  · rintro z hz _ ⟨f, hf, rfl⟩
    exact ⟨_, pol_Dp hB (at_mul' hz _) hf, SchwartzMap.ext fun y => (hT _ y).trans (h.slice (hT f) z y)⟩

end Adp

end PositivityTheory.ThKF0
end
end
end
