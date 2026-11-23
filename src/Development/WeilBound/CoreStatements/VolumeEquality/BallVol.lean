module

public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolArith
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne
public import Development.WeilBound.CoreStatements.VolumeEquality.LocInj
import Development.WeilBound.CoreStatements.VolumeEquality.LocInjA
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
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LevelIdeal
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolLevel
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SkewHermitianFormExists
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolMoeb
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugateUniversalFamily
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.VolumeEquality.BallVolStdZ

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.BallVolFam

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sgU_of_iso {j j' N : ℕ} (s : E →+* ℂ) {G G' a : Matrix (Fin N) (Fin N) E} (ha : aᵀ * G * a.map (ccH E) = G')
    {A A' : Matrix (Fin N) (Sg j j') ℂ} {Ai : Matrix (Sg j j') (Fin N) ℂ} (hA : Aᴴ * (G.map s)ᵀ * A = sgI j j')
    (hA' : A'ᴴ * (G'.map s)ᵀ * A' = sgI j j') (hi : A * Ai = 1) : IsSgU (Ai * (a.map s * A')) := by
  have e2 : ((a.map (ccH E)).map s)ᵀ = (a.map s)ᴴ := by
    ext i k
    exact IsCMField.complexEmbedding_complexConj E s _
  have e3 : (a.map s)ᴴ * (G.map s)ᵀ * a.map s = (G'.map s)ᵀ := by
    rw [← ha, Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul, e2, Matrix.transpose_map, transpose_transpose,
      Matrix.mul_assoc]
  have e4 : A * (Ai * (a.map s * A')) = a.map s * A' := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  unfold IsSgU
  calc _ = (A * (Ai * (a.map s * A')))ᴴ * (G.map s)ᵀ * (A * (Ai * (a.map s * A'))) := by
        rw [← hA, conjTranspose_mul A]
        simp only [Matrix.mul_assoc]
    _ = A'ᴴ * ((a.map s)ᴴ * (G.map s)ᵀ * a.map s) * A' := by
        rw [e4, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e3, hA']

theorem InLevel.form {H : Host E} {l : Level H} {D : Datum H} {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ)
    {form : D.La →ₗ[ℤ] D.La →ₗ[ℤ] ℤ} (hF : form = D.EF ∨ form = -D.EF) (u v : D.La) : form (γ u) (γ v) = form u v := by
  rcases hF with e | e
  · rw [e]
    exact h.1 u v
  · rw [e]
    exact congrArg Neg.neg (h.1 u v)

theorem InLevel.free {H : Host E} {l : Level H} {D : Datum H} {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ) {g : ℕ}
    (R : RiemLat E g D.La) (hF : R.form = D.EF ∨ R.form = -D.EF) (he : R.EqvBy R γ) (v : D.La) : γ v = v := by
  refine rigid_of_congr (reForm R) (reForm_pos _) (fun C => ?_) γ.toLinearMap.toAddMonoidHom
    (reForm_eqv (h.form hF) he) l.M l.three_le h.congr v
  obtain ⟨S, hS₁, hS₂⟩ := short_finite (fun _ : Unit => R) (fun _ => continuous_const) continuous_const () C
  exact hS₁.subset hS₂.self_of_nhds

theorem mfund_of {H : Host E} {l : Level H} {D : Datum H} {Ψ : Type} [Fintype Ψ] {j j' n g N : ℕ}
    {F : UnivFam E Ψ j j' n g D.La} {Γ : Subgroup (D.La ≃ₗ[𝓞 E] D.La)} {FF : Set (Fin n → ℂ)}
    (hF : F.form = D.EF ∨ F.form = -D.EF) (hΓ : ∀ γ, γ ∈ Γ ↔ InLevel l D γ) (hFF : F.IsFundSet Γ FF)
    {e : D.La →ₗ[𝓞 E] (Fin N → E)} (hL : IsLat (LinearMap.range e)) {Γm : Subgroup (GL (Fin N) E)}
    {ρ : GL (Fin N) E → Ψ → Matrix (Sg j j') (Sg j j') ℂ} {Z : (Fin n → ℂ) → Fin n → ℂ}
    (hZ : Set.BijOn Z (ballDom F.q) (ballDom F.q)) (hm : MeasurableSet (Z '' FF))
    (hq : ∀ γ ∈ Γm, ∀ δ : D.La ≃ₗ[𝓞 E] D.La, (∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) →
      ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔ Z t' = moebBall F.q (ρ γ) (Z t)))
    (h1 : ∀ γ ∈ Γm, ∃ δ, InLevel l D δ ∧ ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x)
    (h2 : ∀ δ, InLevel l D δ → ∃ γ ∈ Γm, ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) :
    MFund F.q ρ Γm (Z '' FF) := by
  refine ⟨hm, ?_, fun s hs => ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hZ.mapsTo (hFF.2.1 ht)
  · obtain ⟨t, ht, rfl⟩ := hZ.surjOn hs
    obtain ⟨t', ht', δ, hδ, he⟩ := hFF.2.2.1 t ht
    obtain ⟨γ, hγ, hx⟩ := h2 δ ((hΓ δ).1 hδ)
    exact ⟨γ, hγ, t', ht', (hq γ hγ δ hx t ht t' (hFF.2.1 ht')).1 he⟩
  · rintro _ ⟨t, ht, rfl⟩ γ hγ ⟨t', ht', he⟩
    obtain ⟨δ, hδ, hx⟩ := h1 γ hγ
    have h3 := (hq γ hγ δ hx t (hFF.2.1 ht) t' (hFF.2.1 ht')).2 he
    obtain rfl := hFF.2.2.2 t ht t' ht' ⟨δ, (hΓ δ).2 hδ, h3⟩
    have h4 := hδ.free (F.R t) (by rw [F.form_eq]; exact hF) h3
    have h5 : Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E) = LinearMap.id := by
      refine LinearMap.ext_on hL.2 ?_
      rintro _ ⟨x, rfl⟩
      rw [Matrix.toLin'_apply, ← hx, h4]
      rfl
    exact Units.ext (Matrix.toLin'.injective (h5.trans Matrix.toLin'_one.symm))

theorem famVol_of (h1 : MoebVol) (h2 : StdModel) (h3 : ArithIdx) (h4 : LevelDict) : FamVol := by
  intro E _ _ _ H l D D' Ψ _ j j' n g F F' Γ Γ' FF FF' c₀ hj hj' hr hc hσ hrt hF hF' hΓ hΓ' hFF hFF'
  have := H.unram
  have hemb : ∀ (u : 𝓞 E →+* ℂ) (x : 𝓞 E), embOf u (x : E) = u x := fun u x => IsFractionRing.lift_algebraMap _ x
  have hext : ∀ u : E →+* ℂ, embOf (u.comp (algebraMap (𝓞 E) E)) = u := fun u =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => hemb _ x)
  have hcov : ∀ u : E →+* ℂ, u ∈ Set.range (fun τ => embOf (F.σ τ)) ∨
      ComplexEmbedding.conjugate u ∈ Set.range (fun τ => embOf (F.σ τ)) := fun u => by
    by_cases h : ∃ τ, F.σ τ = (starRingEnd ℂ).comp (u.comp (algebraMap (𝓞 E) E))
    · obtain ⟨τ, hτ⟩ := h
      exact Or.inr ⟨τ, (congrArg embOf hτ).trans (hext (ComplexEmbedding.conjugate u))⟩
    · obtain ⟨τ, hτ⟩ := (F.cm.2 _).2 h
      exact Or.inl ⟨τ, (congrArg embOf hτ).trans (hext u)⟩
  have hne : Nonempty Ψ := by
    obtain ⟨u⟩ : Nonempty (E →+* ℂ) := inferInstance
    rcases hcov u with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩
  have hξ : ∀ τ, embOf (F.σ τ) (H.rt : E) = Complex.I * (c₀ : ℂ) := fun τ => (hemb _ _).trans (hrt τ)
  obtain ⟨τ₀⟩ := hne
  have : Nonempty Ψ := ⟨τ₀⟩
  have hξ0 : -(H.rt : E) ≠ 0 := neg_ne_zero.2 fun h => by
    have := hξ τ₀
    rw [h, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 hc.ne') this.symm
  have hξc : cc (-(H.rt : E)) = - -(H.rt : E) := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, neg_neg, map_neg, hξ]
    simp)
  obtain ⟨G, e, A, Ai, Z, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h2 E Ψ j j' n g _ H F _ c₀ hc hξ
  obtain ⟨G', e', A', Ai', Z', b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2 E Ψ j j' n g _ H F' _ c₀ hc (hσ ▸ hξ)
  rw [hσ] at b6 b9
  obtain ⟨c1, c2, c3⟩ := h4 E H l D _ G e _ _ hF a3 a4 hξ0 a5
  obtain ⟨d1, d2, d3⟩ := h4 E H l D' _ G' e' _ _ hF' b3 b4 hξ0 b5
  have hne : levIdeal l ≠ ⊥ :=
    inf_span_ne_bot l.prod (Nat.cast_ne_zero.2 (by have := l.three_le; omega)) (Nat.cast_ne_zero.2 l.A_pos.ne')
  obtain ⟨a, ha, hle, hidx⟩ := h3 E Ψ j j' _ G G' _ _ _ (levIdeal l) hcov hj hj' hr a1 b1 a2 b2 (fun τ => ⟨_, (a6 τ).1⟩)
    (fun τ => ⟨_, (b6 τ).1⟩) a4 b4 hξ0 hξc c1 d1 hne
    (neat_mono inf_le_left (neat_of_split E H.bar H.bar_eq l.M l.Mb l.three_le l.prod l.coprime))
  obtain ⟨m1, m2⟩ := a8 FF hFF.1 hFF.2.1
  obtain ⟨m3, m4⟩ := b8 FF' hFF'.1 hFF'.2.1
  have f1 := mfund_of (Γm := levelGrp (ccH E) G (LinearMap.range e) (levIdeal l)) hF hΓ hFF a4 a7 m1
    (fun γ hγ => a9 γ (Subgroup.mem_inf.1 hγ).1) c2 c3
  have f2 := mfund_of (Γm := levelGrp (ccH E) G' (LinearMap.range e') (levIdeal l)) hF' hΓ' hFF' b4 b7 m3
    (fun γ hγ => b9 γ (Subgroup.mem_inf.1 hγ).1) d2 d3
  have : Countable (Matrix (Fin (j + j')) (Fin (j + j')) E) := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.countable_iff.2 inferInstance
    exact inferInstanceAs (Countable (Fin (j + j') → Fin (j + j') → E))
  have : Countable (GL (Fin (j + j')) E) :=
    (Units.val_injective.countable : Countable (Matrix (Fin (j + j')) (Fin (j + j')) E)ˣ)
  have canc : ∀ τ (X : Matrix (Fin (j + j')) (Sg j j') ℂ), A τ * (Ai τ * X) = X := fun τ X => by
    rw [← Matrix.mul_assoc, (a6 τ).2.2, Matrix.one_mul]
  have canc' : ∀ τ (X : Matrix (Fin (j + j')) (Sg j j') ℂ), A' τ * (Ai' τ * X) = X := fun τ X => by
    rw [← Matrix.mul_assoc, (b6 τ).2.2, Matrix.one_mul]
  rw [← m2, ← m4]
  refine h1 Ψ j j' n F.q F'.q _ (rho (fun τ => embOf (F.σ τ)) A Ai) (rho (fun τ => embOf (F.σ τ)) A' Ai')
    (fun τ => Ai τ * ((a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) * A' τ)) (uGrp (ccH E) G)
    (levelGrp (ccH E) G (LinearMap.range e) (levIdeal l)) (levelGrp (ccH E) G' (LinearMap.range e') (levIdeal l)) a _ _
    (fun τ => ?_) (fun x y τ => ?_) (fun γ hγ τ => sgU_of_iso _ hγ (a6 τ).1 (a6 τ).1 (a6 τ).2.2)
    (fun γ hγ τ => sgU_of_iso _ (Subgroup.mem_inf.1 hγ).1 (b6 τ).1 (b6 τ).1 (b6 τ).2.2) (fun τ => sgU_of_iso _ ha (a6 τ).1 (b6 τ).1 (a6 τ).2.2)
    (fun γ τ => ?_) inf_le_left hle hidx f1 f2
  · rw [rho, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, (a6 τ).2.1]
  · simp only [rho, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, canc]
  · have : ((a⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) *
        ((a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) * A' τ) = A' τ := by
      rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    simp only [rho, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc, canc, canc', this]

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.BallVolModel

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

theorem qconj_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (x : E) :
    GroundTheory.Automorphic.conj (maximalRealSubfield E) E x = IsCMField.complexConj E x :=
  HermTrace.quadConj_eq_complexConj x

theorem sesq_eq_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    (h : GroundTheory.Automorphic.HermitianForm (maximalRealSubfield E) E (Fin N → E)) (r : E) (x y : Fin N → E) :
    herm (r • (GroundTheory.Automorphic.gram h.toSesq (Pi.basisFun E (Fin N)))ᵀ) x y = r * h.toSesq y x := by
  rw [GroundTheory.Automorphic.sesq_eq_sum h.toSesq (Pi.basisFun E (Fin N)), herm, Finset.sum_comm]
  simp only [Finset.mul_sum, qconj_eq, Pi.basisFun_repr, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, cc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem sgI_sq (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem stdModel_of (h : StdZ) : StdModel := by
  intro E _ _ _ Ψ _ _ j j' n g Λ _ _ H F ξ c₀ hc₀ hξ
  obtain ⟨C⟩ := GlobalTheory.T.exists_lattice_embedding E Ψ j j' n g Λ H F
  obtain ⟨A, hA, Z, hbij, hmeas, hZ⟩ := h E Ψ j j' n g Λ F C
  obtain ⟨τ₀⟩ := ‹Nonempty Ψ›
  have hc := C.c_pos
  have hc₀' : (c₀ : ℂ) ≠ 0 := by exact_mod_cast hc₀.ne'
  have hξ0 : ξ ≠ 0 := fun h0 => by
    have := hξ τ₀
    rw [h0, map_zero] at this
    exact mul_ne_zero Complex.I_ne_zero hc₀' this.symm
  set r : E := C.xi / ξ with hr
  have hsr : ∀ τ, embOf (F.σ τ) r = ((C.c / c₀ * C.eps τ : ℝ) : ℂ) := fun τ => by
    rw [hr, map_div₀, C.xi_eq, hξ]
    push_cast
    field_simp
  have heps : ∀ τ, C.eps τ ≠ 0 := fun τ h0 => by
    have := C.eps_sq τ
    rw [h0] at this
    norm_num at this
  have hsr0 : ∀ τ, embOf (F.σ τ) r ≠ 0 := fun τ => by
    rw [hsr]
    exact_mod_cast mul_ne_zero (div_pos hc hc₀).ne' (heps τ)
  have hr0 : r ≠ 0 := fun h0 => hsr0 τ₀ (by rw [h0, map_zero])
  have hcr : cc r = r := (embOf (F.σ τ₀)).injective (by
    rw [cc, IsCMField.complexEmbedding_complexConj, hsr, Complex.conj_ofReal])
  set g₀ := GroundTheory.Automorphic.gram C.h.toSesq (Pi.basisFun E (Fin (j + j'))) with hg₀
  have hGs : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = embOf (F.σ τ) r • C.gr τ := fun τ => by
    ext a b
    simp [LatEmb.gr, hg₀]
  have hGs' : ∀ τ, ((r • g₀ᵀ).map (embOf (F.σ τ)))ᵀ = ((C.c / c₀ : ℝ) : ℂ) • C.sgr τ := fun τ => by
    rw [hGs, hsr, LatEmb.sgr, smul_smul, Complex.ofReal_mul]
  let e : Λ →ₗ[𝓞 E] (Fin (j + j') → E) :=
    { toFun := C.e, map_add' := C.e.map_add, map_smul' := fun a x => C.e_smul a x }
  let k : ℝ := Real.sqrt (c₀ / C.c)
  have hk : 0 < k := Real.sqrt_pos.2 (div_pos hc₀ hc)
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkk : (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) * k = 1 := by
    have : k * (C.c / c₀) * k = 1 := by
      have h1 : k * k = c₀ / C.c := Real.mul_self_sqrt (div_pos hc₀ hc).le
      rw [mul_right_comm, h1]
      field_simp
    exact_mod_cast this
  have hl : ∀ τ, C.cinv (A τ) τ * A τ = 1 := fun τ => by
    rw [LatEmb.cinv, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A τ)ᴴ, hA, sgI_sq]
  have hrr : ∀ τ, A τ * C.cinv (A τ) τ = 1 := fun τ =>
    (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (hl τ)
  have hform : ∀ x y, ((F.form x y : ℤ) : ℚ) = EFf (-ξ) (r • g₀ᵀ) (e x) (e y) := fun x y => by
    rw [C.form_eq, EFf, hg₀, sesq_eq_herm, neg_neg, ← mul_assoc, hr, mul_div_cancel₀ _ hξ0]
    rfl
  refine ⟨r • g₀ᵀ, e, fun τ => (k : ℂ) • A τ, fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ, Z, fun a b => ?_, ?_, C.e_inj, ⟨?_, ?_⟩,
    hform, fun τ => ⟨?_, ?_, ?_⟩, hbij, hmeas, fun γ hγ δ hδ t ht t' ht' => ?_⟩
  · have h1 : cc (g₀ b a) = g₀ a b := by
      rw [cc, ← qconj_eq]
      exact C.h.isSymm.eq _ _
    show cc (r * g₀ b a) = r * g₀ a b
    rw [← h1]
    conv_rhs => rw [← hcr]
    exact map_mul (IsCMField.complexConj E) _ _
  · rw [det_smul, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr0) (GroundTheory.Automorphic.isUnit_det_gram C.h _).ne_zero
  · have := (F.R 0).fin
    have : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ _ _
    exact Module.Finite.iff_fg.1 inferInstance
  · exact C.integral.isLattice.span_eq_top
  · rw [hGs', conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      hA, smul_smul, smul_smul]
    have : star (k : ℂ) * (k : ℂ) * ((C.c / c₀ : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_ofReal, mul_right_comm, hkk]
    rw [this, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hl, smul_smul, inv_mul_cancel₀ hk', one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hrr, smul_smul, mul_inv_cancel₀ hk', one_smul]
  · have hγ' : (γ : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * (r • g₀ᵀ) *
        (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = r • g₀ᵀ := hγ
    have hrho : rho (fun τ => embOf (F.σ τ)) (fun τ => (k : ℂ) • A τ) (fun τ => (k : ℂ)⁻¹ • C.cinv (A τ) τ) γ =
        rho (fun τ => embOf (F.σ τ)) A (fun τ => C.cinv (A τ) τ) γ := by
      funext τ
      simp only [rho]
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hk', one_smul]
    rw [hrho]
    refine hZ γ δ hδ (fun x y => ?_) (fun τ => ?_) t ht t' ht'
    · have h1 := hform (δ x) (δ y)
      rw [hδ, hδ, EFf, herm_mulVec', hγ', ← EFf, ← hform] at h1
      exact_mod_cast h1
    · have h1 := congrArg (fun M => (M.map (embOf (F.σ τ)))ᵀ) hγ'
      have h2 : (((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E)).map (embOf (F.σ τ)))ᵀ =
          ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)))ᴴ := by
        ext a b
        exact IsCMField.complexEmbedding_complexConj E (embOf (F.σ τ)) ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E) b a)
      simp only [Matrix.map_mul, transpose_mul] at h1
      rw [hGs, h2, ← Matrix.transpose_map, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul] at h1
      rw [Matrix.mul_assoc]
      exact smul_right_injective _ (hsr0 τ) h1

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.BallVolRed

section

@[expose] public section

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
  GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam
open scoped ComplexOrder

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)

def permQ (π : Ψ ≃ Ψ) : Ψ × Fin j × Fin j' ≃ Fin n := (π.prodCongr (Equiv.refl _)).trans q

theorem ballDom_permQ (π : Ψ ≃ Ψ) : ballDom (permQ q π) = ballDom q :=
  Set.ext fun t => ⟨fun h τ => by
    obtain ⟨τ, rfl⟩ := π.surjective τ
    exact h τ, fun h τ => h (π τ)⟩

theorem ballPot_permQ (π : Ψ ≃ Ψ) (t : Fin n → ℂ) : ballPot (permQ q π) t = ballPot q t :=
  congrArg Neg.neg (π.sum_comp fun τ => Real.log (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re)

theorem ballMeas_permQ (π : Ψ ≃ Ψ) : ballMeas (permQ q π) = ballMeas q := by
  simp only [ballMeas, ballDens, ballDom_permQ, ballPot_permQ]

theorem star_measurePreserving : MeasurePreserving (star : (Fin n → ℂ) → Fin n → ℂ) volume volume :=
  volume_preserving_pi (f := fun _ => Complex.conjLIE) fun _ => Complex.conjLIE.measurePreserving

theorem ballMeas_star {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ballMeas q (star ⁻¹' S) = ballMeas q S := by
  have hemb : MeasurableEmbedding (star : (Fin n → ℂ) → Fin n → ℂ) :=
    (Homeomorph.mk ⟨star, star, star_star, star_star⟩ continuous_star continuous_star).measurableEmbedding
  rw [ballMeas_apply q hS hD, ballMeas_apply q (hemb.measurable hS)
    (fun t ht => by simpa using star_mem_ballDom (hD ht)),
    ← star_measurePreserving.setLIntegral_comp_preimage_emb hemb _ S]
  simp only [ballDens, ballPot_star]

theorem integral_ballDens {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hD : S ⊆ ballDom q) :
    ∫ t in S, ballDens q t = (ballMeas q S).toReal := by
  rw [ballMeas_apply q hS hD]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
    (DictMeas.measurable_ballDens q).aestronglyMeasurable

end Ball

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

def permFam (F : UnivFam E Ψ j j' n g Λ) (π : Ψ ≃ Ψ) : UnivFam E Ψ j j' n g Λ where
  q := permQ F.q π
  σ τ := F.σ (π τ)
  cm := ⟨F.cm.1.comp π.injective, fun s => by
    rw [π.exists_congr_right (q := fun τ => F.σ τ = s),
      π.exists_congr_right (q := fun τ => F.σ τ = (starRingEnd ℂ).comp s)]
    exact F.cm.2 s⟩
  form := F.form
  R := F.R
  form_eq := F.form_eq
  hol := by rw [ballDom_permQ]; exact F.hol
  sig t ht τ := F.sig t (ballDom_permQ F.q π ▸ ht) (π τ)
  b τ := F.b (π τ)
  frames := by
    rw [ballDom_permQ]
    exact ⟨fun τ => F.frames.1 (π τ), fun t ht τ => F.frames.2 t ht (π τ)⟩
  logDet_eq t ht := by
    rw [ballPot_permQ, ← F.logDet_eq t (ballDom_permQ F.q π ▸ ht)]
    exact π.sum_comp fun τ => Real.log ((F.R t).gram fun i => F.b τ i t).det.re
  univ R' hf hs := by
    rw [ballDom_permQ]
    exact F.univ R' hf fun τ => by
      obtain ⟨τ, rfl⟩ := π.surjective τ
      exact hs τ

theorem permFam_fund {F : UnivFam E Ψ j j' n g Λ} (π : Ψ ≃ Ψ) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (permFam F π).IsFundSet Γ FF := by
  have e : ballDom (permFam F π).q = ballDom F.q := ballDom_permQ F.q π
  unfold UnivFam.IsFundSet
  rw [e]
  exact h

theorem conjFam_fund {F : UnivFam E Ψ j j' n g Λ} {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)}
    (h : F.IsFundSet Γ FF) : (conjFam F).IsFundSet Γ (star ⁻¹' FF) := by
  refine ⟨continuous_star.measurable h.1, fun t ht => ?_, fun t ht => ?_, fun t ht t' ht' ⟨γ, hγ, he⟩ => ?_⟩
  · show t ∈ ballDom F.q
    simpa using star_mem_ballDom (h.2.1 ht)
  · obtain ⟨t', ht', γ, hγ, he⟩ := h.2.2.1 (star t) (star_mem_ballDom (q := F.q) ht)
    refine ⟨star t', by simpa using ht', γ, hγ, eqvBy_conj (fun x => rfl) (fun x => ?_) he⟩
    show star ((F.R (star (star t'))).P x) = _
    rw [star_star]
  · refine star_injective (h.2.2.2 _ ht _ ht' ⟨γ, hγ, eqvBy_conj (fun x => ?_) (fun x => ?_) he⟩)
    · exact (star_star _).symm
    · exact (star_star _).symm

theorem normalise (F : UnivFam E Ψ j j' n g Λ) (r : 𝓞 E) (d : ℕ) (hr : r ^ 2 = -(d : 𝓞 E))
    (hc : ∀ τ τ', F.σ τ r = F.σ τ' r) {Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)} {FF : Set (Fin n → ℂ)} (h : F.IsFundSet Γ FF) :
    ∃ (F₁ : UnivFam E Ψ j j' n g Λ) (FF₁ : Set (Fin n → ℂ)), (∀ τ, F₁.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ∧
      (F₁.form = F.form ∨ F₁.form = -F.form) ∧ F₁.IsFundSet Γ FF₁ ∧ ballMeas F₁.q FF₁ = ballMeas F.q FF := by
  by_cases h0 : ∀ τ, F.σ τ r = Complex.I * ((Real.sqrt d : ℝ) : ℂ)
  · exact ⟨F, FF, h0, Or.inl rfl, h, rfl⟩
  · obtain ⟨τ₀, h1⟩ := not_forall.1 h0
    have h2 : F.σ τ₀ r ^ 2 = (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 := by
      rw [← map_pow, hr, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      simp
    have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_left h1
    refine ⟨conjFam F, star ⁻¹' FF, fun τ => ?_, Or.inr rfl, conjFam_fund h, ballMeas_star F.q h.1 h.2.1⟩
    show starRingEnd ℂ (F.σ τ r) = _
    rw [hc τ τ₀, h3]
    simp

omit [NumberField E] [IsCMField E] in
theorem exists_perm {σ σ' : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) (h' : IsCMFam σ') (r : 𝓞 E) {c : ℝ} (hc : 0 < c)
    (hs : ∀ τ, σ τ r = Complex.I * (c : ℂ)) (hs' : ∀ τ, σ' τ r = Complex.I * (c : ℂ)) :
    ∃ π : Ψ ≃ Ψ, ∀ τ, σ' (π τ) = σ τ := by
  have : ∀ τ, ∃ τ', σ' τ' = σ τ := fun τ => (h'.2 _).2 fun ⟨τ', e⟩ => by
    have e1 := hs' τ'
    rw [e, RingHom.comp_apply, hs] at e1
    have := congrArg Complex.im e1
    simp at this
    linarith
  choose f hf using this
  have hi : Function.Injective f := fun a b e => h.1 (by rw [← hf, ← hf, e])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hi), hf⟩

theorem label_rt {H : Host E} {l : Level H} (c : Coeff l) (τ τ' : CMType H) :
    labelEmb c (.inr τ) H.rt = labelEmb c (.inr τ') H.rt := by
  refine Subtype.ext ?_
  show τ.1 ((H.bar H.rt : 𝓞 E) : E) = τ'.1 ((H.bar H.rt : 𝓞 E) : E)
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, IsCMField.complexEmbedding_complexConj, τ.2, τ'.2]

theorem ballVolEq_of (h : FamVol) : BallVolEq := by
  intro _ E _ _ _ _ H D l Xo c Y n B FF hq hp hF k k'
  have hn := fun k => normalise (B.F k) H.rt H.d H.rt_sq
    (fun τ τ' => by rw [B.σ_eq, B.σ_eq, RingHom.comp_apply, RingHom.comp_apply, label_rt c τ τ']) (hF k)
  obtain ⟨F₁, FF₁, s₁, f₁, u₁, m₁⟩ := hn k
  obtain ⟨F₂, FF₂, s₂, f₂, u₂, m₂⟩ := hn k'
  have hd : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
  obtain ⟨π, hπ⟩ := exists_perm F₁.cm F₂.cm H.rt hd s₁ s₂
  have hf : ∀ k (f : _ →ₗ[ℤ] _ →ₗ[ℤ] ℤ), (f = (B.F k).form ∨ f = -(B.F k).form) → f = (B.Di k).EF ∨ f = -(B.Di k).EF := by
    intro k f hf
    rcases hf with rfl | rfl <;> rcases B.form_eq k with e | e <;> rw [e] <;> simp
  have key := h E H l (B.Di k) (B.Di k') (CMType H) D.p D.q n B.g F₁ (permFam F₂ π) (B.Γ k) (B.Γ k') FF₁ FF₂ _
    (by omega) (by omega) (by omega) hd (funext hπ) s₁ (hf k _ f₁) (hf k' _ f₂) (B.mem_Γ k) (B.mem_Γ k') u₁
    (permFam_fund π u₂)
  rw [integral_ballDens _ (hF k).1 (hF k).2.1, integral_ballDens _ (hF k').1 (hF k').2.1, ← m₁, ← m₂, key]
  exact congrArg (fun μ : Measure (Fin n → ℂ) => (μ FF₂).toReal) (ballMeas_permQ F₂.q π)

end SheetDecomposition
end
end
end

-- Source module: Development.WeilBound.CoreStatements.VolumeEquality.BallVol

section

@[expose] public section

namespace SheetDecomposition

theorem famVol : FamVol := famVol_of moebVol (stdModel_of stdZ) arithIdx levelDict

theorem ballVolEq : BallVolEq := ballVolEq_of famVol

end SheetDecomposition
end
end
