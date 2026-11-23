module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullLinInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceOfFaceCutStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellOfQuotientCellRadicalPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientRadicalConeStatement

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGalois

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction

theorem twEval_of_isTwG {O : Type} [CommRing O] {w0 : O} {ψ : InvFun O}
    (htw : IsTwG w0 ψ) {σ : O ≃+* O} (hσ : σ w0 = w0) : Tw.TwEval σ ψ := by
  intro Y Y' _ _ _ _ _ _ τ hτ B
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O Y
  have hsy : ∀ (a : O) (y : Y), τ.symm (σ a • y) = a • τ.symm y := fun a y => by
    apply τ.injective
    rw [hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let s' : (Fin n → O) →ₗ[O] Y' :=
    { toFun := fun x => τ.symm (s fun i => σ (x i))
      map_add' := fun x x' => by
        have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := by ext i; simp
        rw [this, map_add (f := _), map_add (f := _)]
      map_smul' := fun c x => by
        have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := by ext i; simp
        rw [this, map_smul, hsy]
        rfl }
  have hs' : Function.Surjective s' := fun y => by
    obtain ⟨x, hx⟩ := hs (τ y)
    refine ⟨fun i => σ.symm (x i), ?_⟩
    show τ.symm (s fun i => σ (σ.symm (x i))) = y
    simp only [RingEquiv.apply_symm_apply]
    rw [hx, AddEquiv.symm_apply_apply]
  rw [ψ.eval_eq hs', ψ.eval_eq hs]
  have := htw σ hσ n fun a b => B (s a) (s b)
  simpa [s'] using this

theorem isTwG_carFun : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  intro O _ _ _ _ bar w0 hb ψ htw σ hσ n B
  have hc : ∀ a, σ (bar a) = bar (σ a) := hb.comm σ
  have hev : Tw.TwEval σ ψ := twEval_of_isTwG htw hσ
  let τ : (Fin n → O) ≃+ (Fin n → O) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hτ : ∀ (a : O) (y : Fin n → O), τ (a • y) = σ a • τ y := fun a y => by ext i; simp [τ]
  have hτs := Tw.symm_smul hτ
  have hcs := Tw.symm_comm hc
  show (carFun bar ψ).toFun n (fun a b => B (τ a) (τ b)) = (carFun bar ψ).toFun n B
  dsimp only [carFun]
  by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b
  · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b :=
      ⟨Tw.pullA τ h.choose, Tw.pullA_mem hc hτ h.choose_spec.1, fun y => h.choose_spec.2.1 _,
        fun a b => h.choose_spec.2.2 _ _⟩
    rw [dite_eq_left h, dite_eq_left h']
    have e : h'.choose = Tw.pullA τ h.choose := LinearMap.ext₂ fun a b => by
      have h1 := h'.choose_spec.2.2 a b
      have h2 := h.choose_spec.2.2 (τ a) (τ b)
      rw [Tw.pullA_apply]
      exact_mod_cast h1.symm.trans h2
    rw [e]
    unfold cdimQ
    congr 2
    refine (Set.Subset.antisymm ?_ (Tw.cdimSet_subset hc hev hτ _))
    have := Tw.cdimSet_subset (bar := bar) (ψ := ψ) hcs hev.symm hτs (Tw.pullA τ h.choose)
    rwa [Tw.pullA_symm_pullA] at this
  · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b := by
      rintro ⟨β, h1, h2, h3⟩
      refine h ⟨Tw.pullA τ.symm β, Tw.pullA_mem hcs hτs h1, fun y => h2 _, fun a b => ?_⟩
      rw [Tw.pullA_apply, ← h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGaloisStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.carrier_function_twisted_galois : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction.isTwG_carFun <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCell

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell

theorem projective_quot_orad (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (X : Type)
    [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) :
    Module.Projective O (X ⧸ (orad β : Submodule O X)) := by
  classical
  have hZ : ∀ n : ℤ, n ≠ 0 → ∀ y : X, n • y ∈ (orad β : Submodule O X) → y ∈ (orad β : Submodule O X) :=
    fun n hn y hy a z => by
      have h := hy a z
      rw [smul_comm, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hn
  have hO : ∀ a : O, a ≠ 0 → ∀ y : X, a • y ∈ (orad β : Submodule O X) → y ∈ (orad β : Submodule O X) := by
    intro a ha y hy
    have hne : (Ideal.span {a}).comap (algebraMap ℤ O) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha (Ideal.mem_span_singleton_self a) (Algebra.IsIntegral.isIntegral a)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hn)
    refine hZ n hn0 y fun b z => ?_
    have h := hy (b * a') z
    rw [mul_smul, smul_smul a' a y, ha', algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul] at h
    exact h
  have htor : Submodule.torsion O (X ⧸ (orad β : Submodule O X)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    obtain ⟨⟨a, ha⟩, hau⟩ := (Submodule.mem_torsion_iff u).1 hu
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hau
    rw [Submodule.Quotient.mk_eq_zero]
    exact hO a (nonZeroDivisors.ne_zero ha) y hau
  have : Module.Flat O (X ⧸ (orad β : Submodule O X)) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  have : Module.FinitePresentation O (X ⧸ (orad β : Submodule O X)) := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

theorem cell_of_quot_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], IsPolyFanOn bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ → InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  intro O _ _ _ _ bar hCM ψ X _ _ _ _ hfan hface β hβ hp m' δ hδ hin
  classical
  have : Module.Projective O (X ⧸ (orad (O := O) β)) := projective_quot_orad O X β
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (orad (O := O) β).mkQ LinearMap.id (orad (O := O) β).mkQ_surjective
  have htt : ∀ u, (orad (O := O) β).mkQ (t u) = u := fun u => LinearMap.congr_fun ht u
  have htt' : ∀ u, (Submodule.Quotient.mk (t u) : X ⧸ (orad (O := O) β)) = u := htt
  have hπ : Function.Surjective (orad (O := O) β).mkQ := (orad (O := O) β).mkQ_surjective

  have desc : ∀ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X → (∀ k ∈ (orad (O := O) β), ∀ y, β' k y = 0) →
      pull (orad (O := O) β).mkQ (pull t β') = β' := by
    intro β' hb hv
    refine LinearMap.ext₂ fun a b => ?_
    have ha : a - t ((orad (O := O) β).mkQ a) ∈ (orad (O := O) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := O) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have hb' : b - t ((orad (O := O) β).mkQ b) ∈ (orad (O := O) β) := by
      rw [← Submodule.Quotient.mk_eq_zero (orad (O := O) β), ← Submodule.mkQ_apply, map_sub, htt, sub_self]
    have e1 := hv _ ha b
    have e2 := hv _ hb' (t ((orad (O := O) β).mkQ a))
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1 e2
    rw [pull_apply, pull_apply, hb.1 (t _) (t _), ← e2, hb.1 b (t ((orad (O := O) β).mkQ a)), ← e1]
  have hbK : ∀ k ∈ (orad (O := O) β), ∀ y, β k y = 0 := fun k hk y => by simpa using (mem_orad.1 hk) 1 y

  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, d, hγ, -, hd, he⟩ := hS _ hmem
  set σ : Fin m → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hσdef
  have hσ : IsCell bar ψ σ := isCell_pull_equiv hγ e.symm
  have hβσ : toReal β = ∑ i, d i • toReal (σ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply, hσdef] using this

  obtain ⟨Nδ, ℓδ, hNδ, hℓδ1, hℓδ2, hℓδ3⟩ := hδ.strict
  obtain ⟨Nσ, ℓσ, hNσ, hℓσ1, hℓσ2, hℓσ3⟩ := hσ.strict
  obtain ⟨hK, hKt⟩ := exists_radical_test bar (orad (O := O) β)
  let g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (Nσ : ℤ) • (ℓδ ∘ₗ pullLin t) - (Nδ : ℤ) • ℓσ
  have hg : ∀ β', g β' = Nσ * ℓδ (pull t β') - Nδ * ℓσ β' := fun β' => by simp [g]
  set M : ℤ := ∑ j, |g (σ j)| + 1 with hM
  have hMj : ∀ j, |g (σ j)| < M := fun j => by
    have := Finset.single_le_sum (f := fun j => |g (σ j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let hh : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := g + M • hK
  have hhv : ∀ β', hh β' = g β' + M * hK β' := fun β' => by simp [hh]
  have factA : ∀ j, hK (σ j) = 0 →
      (g (σ j) : ℝ) = Nσ * ((ℓδ (pull t (σ j)) : ℝ) - Nδ * ψ.evalZ (pull t (σ j))) := by
    intro j hj
    have hv := (hKt _ (hσ.mem j) (hσ.nonneg j)).2.1 hj
    have e1 : ψ.evalZ (σ j) = ψ.evalZ (pull t (σ j)) := by
      rw [← evalZ_pull ψ hπ (pull t (σ j)), desc _ (hσ.mem j) hv]
    rw [hg]
    push_cast
    rw [hℓσ1 j, e1]
    ring
  have hpos : ∀ j, hK (σ j) ≠ 0 → 0 < hh (σ j) := by
    intro j hj
    rw [hhv]
    have h0 := (hKt _ (hσ.mem j) (hσ.nonneg j)).1
    have h1 : 1 ≤ hK (σ j) := by omega
    have h2 := hMj j
    have hM0 : 0 ≤ M := (abs_nonneg _).trans h2.le
    have h3 := mul_le_mul_of_nonneg_left h1 hM0
    have h4 := neg_abs_le (g (σ j))
    linarith
  have hnn : ∀ j, 0 ≤ hh (σ j) := by
    intro j
    by_cases hj : hK (σ j) = 0
    · rw [hhv, hj, mul_zero, add_zero]
      have hA := factA j hj
      have h2 := hℓδ2 (pull t (σ j)) (pull_mem t (hσ.mem j)) (fun y => hσ.nonneg j _)
      have h3 : (0 : ℝ) ≤ g (σ j) := by
        rw [hA]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
      exact_mod_cast h3
    · exact (hpos j hj).le

  set F : Finset (Fin m) := Finset.univ.filter fun j => hh (σ j) = 0 with hF
  let s : Fin F.card ↪ Fin m := (F.orderEmbOfFin rfl).toEmbedding
  have hs : ∀ j, j ∈ Set.range s ↔ hh (σ j) = 0 := fun j => by
    have : Set.range s = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    rw [this]
    simp [hF]
  have hcut : IsFaceCut σ s hh := ⟨hnn, fun j => (hs j).symm⟩
  have hσs : IsCell bar ψ (fun i => σ (s i)) := hface m F.card σ s hh hσ hcut

  have hKb : hK β = 0 := (hKt β hβ hp).2.2 hbK
  have hψβ : ψ.evalZ β = ψ.evalZ (pull t β) := by
    rw [← evalZ_pull ψ hπ (pull t β), desc β hβ hbK]
  obtain ⟨c, hc, hcβ⟩ := hin
  have hcβ1 : toReal (pull t β) = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hcβ (t a) (t b)
    simpa [LinearMap.sum_apply, htt, htt'] using this
  have hgβ : g β = 0 := by
    have e1 := intLin_eq_of_inCone ψ hσ.linear hℓσ1 hd hβσ
    have e2 := intLin_eq_of_inCone ψ hδ.linear hℓδ1 hc hcβ1
    have : (g β : ℝ) = 0 := by
      rw [hg]
      push_cast
      rw [e1, e2, hψβ]
      ring
    exact_mod_cast this
  have hhβ : hh β = 0 := by rw [hhv, hgβ, hKb]; simp
  have hsum := intLin_eq_sum_of_toReal σ d β hh hβσ
  rw [hhβ, Int.cast_zero] at hsum
  have hzero : ∀ j, d j * (hh (σ j) : ℝ) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hd j) (by exact_mod_cast hnn j))).1 hsum.symm
    exact fun j => this j (Finset.mem_univ j)
  have hdz : ∀ j, j ∉ Set.range s → d j = 0 := fun j hj => by
    have h0 : (hh (σ j) : ℝ) ≠ 0 := by exact_mod_cast fun h => hj ((hs j).2 h)
    exact (mul_eq_zero.1 (hzero j)).resolve_right h0
  have hcone : InRCone (fun i => σ (s i)) β := by
    refine ⟨fun i => d (s i), fun i => hd _, ?_⟩
    rw [hβσ]
    exact (Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [hdz j hj, zero_smul]) fun i => rfl).symm

  have hspan : ∀ i, ∃ k : ℕ, 0 < k ∧ k • σ (s i) ∈ Submodule.span ℤ (Set.range fun i => pull (orad (O := O) β).mkQ (δ i)) := by
    intro i
    have hj0 : hh (σ (s i)) = 0 := (hs (s i)).1 ⟨i, rfl⟩
    have hKj : hK (σ (s i)) = 0 := by
      by_contra hne
      exact (hpos _ hne).ne' hj0
    have hgj : g (σ (s i)) = 0 := by
      rw [hhv, hKj, mul_zero, add_zero] at hj0
      exact hj0
    have hA := factA _ hKj
    rw [hgj, Int.cast_zero] at hA
    have heq : (Nδ : ℝ) * ψ.evalZ (pull t (σ (s i))) = ℓδ (pull t (σ (s i))) := by
      have hN : (Nσ : ℝ) ≠ 0 := by exact_mod_cast hNσ.ne'
      have := (mul_eq_zero.1 hA.symm).resolve_left hN
      linarith
    obtain ⟨k, c', hk, hkc⟩ := hℓδ3 _ (pull_mem t (hσ.mem (s i))) (fun y => hσ.nonneg (s i) _) heq
    refine ⟨k, hk, ?_⟩
    have hv := (hKt _ (hσ.mem (s i)) (hσ.nonneg (s i))).2.1 hKj
    have e3 : k • σ (s i) = ∑ l, c' l • pull (orad (O := O) β).mkQ (δ l) := by
      have e := congrArg (pullLin (orad (O := O) β).mkQ) hkc

      simp only [map_nsmul, map_sum, pullLin_apply] at e
      rw [desc _ (hσ.mem (s i)) hv] at e
      exact e
    rw [e3]
    exact Submodule.sum_mem _ fun l _ => nsmul_mem (Submodule.subset_span (Set.mem_range_self l)) _
  refine ⟨F.card, fun i => σ (s i), hσs, hcone, ?_⟩
  calc genRank (fun i => σ (s i)) ≤ genRank (fun i => pull (orad (O := O) β).mkQ (δ i)) :=
        genRank_le_of_smul_mem_span _ _ hspan
    _ = genRank δ := genRank_pull hπ δ

end GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellOfQuotientCellStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

theorem _root_.GlobalTheory.T.cell_of_quotient_cell : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], IsPolyFanOn bar ψ X → (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i))) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule O X))), IsCell bar ψ δ → InRCone (fun i => pull (orad β : Submodule O X).mkQ (δ i)) β → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧ genRank γ ≤ genRank δ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell | exact GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.QuotientCell.cell_of_quot_cell <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabel

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension

theorem exists_cell {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {ψ : InvFun O} {X : Type}
    [AddCommGroup X] [Module O X] [Module.Finite O X] (hfan : IsPolyFanOn bar ψ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β := by
  have hmem : toReal β ∈ psdCone (bar := bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hS _ hmem
  refine ⟨m, fun i => pull e.symm.toLinearMap (γ i), isCell_pull_equiv hγ e.symm, c, hc, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
  simpa [LinearMap.sum_apply] using this

theorem exists_isCarrierDim : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ lab : InvFun O, IsTwG w0 lab ∧ IsCarrierDim bar q ψ lab := by
  intro O _ _ _ _ bar w0 hb q ψ hD hψ htw
  refine ⟨carFun bar ψ, GlobalTheory.T.carrier_function_twisted_galois O bar w0 hb ψ htw, ?_⟩
  intro X _ _ _ _ hX β hβ hp
  have hfan := hψ X hX
  have hface := GlobalTheory.T.cell_face_of_face_cut O bar hb ψ X hfan (hD X)
  rw [evalZ_carFun hβ hp]
  congr 1
  obtain ⟨m₀, γ₀, hγ₀, hin₀⟩ := exists_cell hfan hβ hp
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}.Nonempty := ⟨_, m₀, γ₀, hγ₀, hin₀, rfl⟩
  apply le_antisymm
  · obtain ⟨m, γ, h1, h2, h3⟩ := Nat.sInf_mem hne
    obtain ⟨m', δ, k1, k2, k3⟩ := GlobalTheory.T.cell_of_quotient_radical_cone O bar hb ψ X hface β hβ hp m γ h1 h2
    exact (Nat.sInf_le (show genRank δ ∈ cdimSet bar ψ X (orad β) β from ⟨m', δ, k1, k2, rfl⟩)).trans (k3.trans h3.le)
  · have hne' : (cdimSet bar ψ X (orad β) β).Nonempty := by
      obtain ⟨m', δ, k1, k2, -⟩ := GlobalTheory.T.cell_of_quotient_radical_cone O bar hb ψ X hface β hβ hp m₀ γ₀ hγ₀ hin₀
      exact ⟨_, m', δ, k1, k2, rfl⟩
    obtain ⟨m', δ, h1, h2, h3⟩ := Nat.sInf_mem hne'
    obtain ⟨m, γ, k1, k2, k3⟩ := GlobalTheory.T.cell_of_quotient_cell O bar hb ψ X hfan hface β hβ hp m' δ h1 h2
    unfold cdimQ
    rw [← h3]
    exact (Nat.sInf_le (show genRank γ ∈ {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      InRCone γ β ∧ genRank γ = k} from ⟨m, γ, k1, k2, rfl⟩)).trans k3

end GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsCarrierDimensionLabelStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
theorem _root_.GlobalTheory.T.exists_carrier_dimension_label : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → ∃ lab : InvFun O, IsTwG w0 lab ∧ IsCarrierDim bar q ψ lab := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim | exact GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.CarrierDimension.exists_isCarrierDim <;> assumption)
end
end
