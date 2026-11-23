module

public import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLift
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
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
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftDesc

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftDesc

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift

section Desc

variable {LL K : Type} [Field LL] [Field K] (e : LL →+* K)

theorem lin_ext_map {σ : Type} (φ : MvPolynomial σ LL →ₗ[LL] LL) (P : MvPolynomial σ LL) :
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
      (MvPolynomial.map e P) = e (φ P) := by
  induction P using MvPolynomial.induction_on'
  next u a =>
    have h1 : MvPolynomial.map e (MvPolynomial.monomial u a) = e a • MvPolynomial.basisMonomials σ K u := by
      simp only [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have h2 : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : LL) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, Basis.constr_basis, h2, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq]

theorem desc_span {σ : Type} (V : Submodule LL (MvPolynomial σ LL)) {Q : MvPolynomial σ LL}
    (hQ : MvPolynomial.map e Q ∈ Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL)))) : Q ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  let φK : MvPolynomial σ K →ₗ[K] K :=
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
  have h1 : Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL))) ≤ LinearMap.ker φK := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    change φK (MvPolynomial.map e v) = 0
    rw [lin_ext_map e φ v, (Submodule.mem_dualAnnihilator φ).1 hφ v hv, map_zero]
  have h2 : φK (MvPolynomial.map e Q) = 0 := h1 hQ
  rw [lin_ext_map e φ Q] at h2
  exact (map_eq_zero_iff e e.injective).1 h2

theorem dw_desc {r n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin r × Fin n) LL}
    (h : MvPolynomial.map e f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl LL r n ν := by
  rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff] at h ⊢
  refine ⟨MvPolynomial.map_injective e e.injective ?_, fun l j hlj => MvPolynomial.map_injective e e.injective ?_⟩
  · rw [whc_map, h.1]
  · rw [colAddGen_map, MvPolynomial.map_rename, h.2 l j hlj]

theorem dw_span {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl K r n ν ≤
      Submodule.span K (MvPolynomial.map e '' (Formalism.GradedWeylDivisibility.dualWeyl LL r n ν : Set (MvPolynomial (Fin r × Fin n) LL))) := by
  refine (dualWeyl_desc e ν).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, dw_desc e ν hQ, rfl⟩

theorem span_prod_le {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K)) (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL))
    (hM : ∀ s, Ms s ≤ Submodule.span K (MvPolynomial.map e '' (Ns s : Set (MvPolynomial (σ s) LL)))) :
    Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span K (MvPolynomial.map e '' (Submodule.span LL
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} :
          Set (MvPolynomial τ LL))) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ K) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, Q ∈ Ns s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span K (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := K) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), Submodule.subset_span ⟨Q, hQ, rfl⟩, ?_⟩
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hQe s, MvPolynomial.map_rename]

theorem vsp_span {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp K lam0 ≤ Submodule.span K (MvPolynomial.map e '' (Vsp LL lam0 : Set (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL))) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span K (MvPolynomial.map e '' (((if Antitone (lamAt lam0 s) then
        Formalism.GradedWeylDivisibility.dualWeyl LL (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥ : Submodule LL _)) : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL))) := by
    intro s
    split_ifs
    · exact dw_span e _
    · exact bot_le
  exact span_prod_le e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ hM

theorem vtup_span {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) : VtupR P K ≤ Submodule.span K (MvPolynomial.map e '' (VtupR P LL : Set (XR P LL))) :=
  span_prod_le e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    fun v => vsp_span e (P.lam0 v)

theorem span_prod_map {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL)) (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K))
    (h : ∀ s, ∀ x ∈ Ns s, MvPolynomial.map e x ∈ Ms s) {Z : MvPolynomial τ LL}
    (hZ : Z ∈ Submodule.span LL {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}) :
    MvPolynomial.map e Z ∈
      Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (F s), fun s => h s _ (hF s), ?_⟩
    simp only [map_prod, MvPolynomial.map_rename]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mapE_smul]; exact Submodule.smul_mem _ _ hx

theorem vsp_map {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) {x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL}
    (hx : x ∈ Vsp LL lam0) : MvPolynomial.map e x ∈ Vsp K lam0 := by
  refine span_prod_map e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ (fun s y hy => ?_) hx
  split_ifs at hy ⊢
  · exact Formalism.GradedWeylDivisibility.dualWeylMap LL K e _ _ _ y hy
  · rw [(Submodule.mem_bot _).1 hy, map_zero]
    exact Submodule.zero_mem _

theorem vtup_map {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Q : XR P LL} (hQ : Q ∈ VtupR P LL) : MvPolynomial.map e Q ∈ VtupR P K :=
  span_prod_map e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    (fun v _ hy => vsp_map e (P.lam0 v) hy) hQ

end Desc

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem vtupDesc_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : VtupDesc S e := by
  intro β Q hQ
  exact vtup_map D.what₂.embLL _ (desc_span e (VtupR (Hc S β).P D.what₂.LL) (vtup_span e (Hc S β).P hQ))

theorem cmpLiftOf_of_two (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hI : CmpInvOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of S e (vtupDesc_holds S e) hV hI

end Rec

end Formalism.MainNotions.G.CmpJ.PCmpLiftDesc
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftTw

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftTw

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T fT : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {S : StepLevel F E σ J T fT bad} {emb : Tau → E →+* ℂ} {c : ℤ}

theorem tw_triv (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {γ : GL (Fin n) E}
    (hγ : γ ∈ UJ (σ : E →+* E) J) {κ : S.U}
    (h : y0.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y0.1 * κ.1) :
    ∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c = 1 := by
  let xg : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ, ratInU γ hγ⟩
  let xk : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩
  have e1 : xg * y0 * xk = y0 := Subtype.ext h.symm
  have e2 : X.ch xg = 1 := by
    have h3 := congrArg X.ch e1
    rw [map_mul, map_mul, X.ch_U xk κ.2, mul_one] at h3
    exact mul_right_cancel (h3.trans (one_mul _).symm)
  have h4 := X.ch_rat γ hγ xg rfl
  rwa [e2, Units.val_one, one_mul] at h4

theorem detF_tr (γ : GL (Fin n) E) {y y' : Formalism.L2.Forms.Frames (gramC J emb)} (hy : IsTr (atInf emb γ) y' y) :
    detF c y = (∏ τ, (emb τ (γ : Matrix (Fin n) (Fin n) E).det) ^ c) * detF c y' := by
  unfold detF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hy τ, Matrix.det_mul, mul_zpow]
  congr 2
  simp [atInf, RingHom.map_det]

theorem foInv_twist (X : DetTw S emb c) {y0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)} {h : Formalism.L2.Forms.Frames (gramC J emb) → ℂ}
    (hh : FoInv S emb y0 h) : FoInv S emb y0 (fun z => (detF c z)⁻¹ * h z) := by
  intro γ hγ κ hy0 y y' hy
  simp only
  rw [hh γ hγ κ hy0 y y' hy, detF_tr γ hy, tw_triv X hγ hy0, one_mul]
  ring

end Gen

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

def CmpInvRawOf (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : Prop :=
  BlockRationalityField → (∀ β, S.Core e β) → KAat.ChX S → ∀ β rep, RepOk S β rep → ∀ c
    (g : ∀ v, GL (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v)) (γ0 : GL (Fin (D.R.N i)) D.host.E) (κ0 : (S.K β).lev.U),
    γ0 ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
    (∀ v, (rep c).2 v = colSpan ((Hc S β).P.W v) (g v : Matrix (Fin ((Hc S β).P.m + 1)) (Fin ((Hc S β).P.m + 1)) ((Hc S β).P.Qq v))) →
    (S.loc β).IsPt (rep c).1 g (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1) →
    ∀ Q ∈ YInv (Hc S β) e (rep c).1 (rep c).2,
      FoInv (S.K β).lev (embT D) ((S.K β).y c) (fun z =>
        evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D)) (crdB (embT D) (S.loc β).B)
          (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 z))

theorem cmpInvOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hR : CmpInvRawOf S e) : CmpInvOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ
  exact foInv_twist (S.tw β) (hR hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ)

theorem cmpLiftOf_of_raw (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hR : CmpInvRawOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of_two S e hV (cmpInvOf_of_raw S e hR)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLiftTw
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLiftInv

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftInv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift
  Formalism.MainNotions.G.CmpJ.PCmpLiftDesc Formalism.MainNotions.G.CmpJ.PCmpLiftTw

theorem grp2 {Γ : Type} [Group Γ] (b y k : Γ) (h : y = b * y * k) : b = y * k⁻¹ * y⁻¹ := by
  rw [show y * k⁻¹ * y⁻¹ = (b * y * k) * k⁻¹ * y⁻¹ by rw [← h]]
  group

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}



theorem cmpInvRaw_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : CmpInvRawOf S e := by
  intro hS H X β rep hok c g γ0 κ0 hγ0 hL hpt Q hQ γ hγ κ hyc y y' hy
  have Hb := H β
  obtain ⟨x, hx⟩ : ∃ x, x = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 * ((S.K β).y c).1 * κ0.1 :=
    ⟨_, rfl⟩
  rw [← hx] at hpt
  have hxU : x ∈ UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (PStabEq.bc_mem hγ0) ((S.K β).y c).2) (PStabEq.U_le κ0.2)
  have hb : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ =
      ((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹ := grp2 _ _ _ hyc
  have hyU : ((S.K β).y c).1⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * ((S.K β).y c).1 ∈
      (S.K β).lev.U := by
    rw [hb, show ((S.K β).y c).1⁻¹ * (((S.K β).y c).1 * κ.1⁻¹ * ((S.K β).y c).1⁻¹) * ((S.K β).y c).1 = κ.1⁻¹ by group]
    exact (S.K β).lev.U.inv_mem κ.2
  have hδU : γ0 * γ * γ0⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hγ0 hγ) (Subgroup.inv_mem _ hγ0)
  have hδx : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x ∈ (S.K β).lev.U :=
    PStabEq.conj_mem' x ((S.K β).y c).1 γ0 γ κ0 hx hyU
  obtain ⟨⟨γ', hfix⟩, hγ'⟩ := (PStabEq.stab_bij Hb.good Hb.int Hb.hypP (X.hypC β) Hb.bad_p Hb.actB Hb.gam Hb.gamU (rep c).1
    (X.inj β _) (X.onto β _) (rep c).2 g hL ⟨x, hxU⟩ hpt).2 ⟨γ0 * γ * γ0⁻¹, hδU, hδx⟩
  have hgam : (S.loc β).gamI (rep c).1 γ' = γ0 * γ * γ0⁻¹ := congrArg Subtype.val hγ'
  obtain ⟨κa, hκa⟩ := awayEx_of Hb.good (S.K β).lev Hb.gam (rep c).1 γ'
  obtain ⟨r, hr, hr1⟩ := Hb.chi (rep c).1 γ' κa hκa

  have hN : natActR (Hc S β).P D.what₂.LL (blkLL (S.loc β) (sigD D) (tEL D) S.pos ((S.loc β).gamI (rep c).1 γ')) Q = r • Q := by
    apply MvPolynomial.map_injective e e.injective
    have h1 := hQ.2 γ' hfix
    rw [actX_map (S.loc β) (tEL D) S.pos e Hb.actB Hb.pos_emb (rep c).1 γ' Q] at h1
    have hr1' : algebraMap G.O G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O) * e r = 1 := hr1
    rw [mapE_smul e r Q, ← h1, ← algebraMap_smul G.Kf (((Hc S β).lev (rep c).1).χ γ' : G.O), smul_smul, mul_comm (e r), hr1',
      one_smul]

  have e1 : x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x =
      κ0.1⁻¹ * κ.1⁻¹ * κ0.1 := by
    rw [hx, map_mul, map_mul, map_inv, hb]
    group
  have ht : ∀ v ∈ S.bad, bc (prV (E := D.host.E) v) (κa * (κ0⁻¹ * κ * κ0)).1 = 1 := by
    intro v hv
    have hvp := Hb.bad_p v hv
    have a1 := hκa.2 v hvp
    have a2 : bc (prV (E := D.host.E) v) ((S.loc β).yG (rep c).1) = bc (prV (E := D.host.E) v) x := (hpt.1 v hvp).symm
    have key : bc (prV (E := D.host.E) v) κa.1 =
        bc (prV (E := D.host.E) v) (x⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ0 * γ * γ0⁻¹) * x) := by
      rw [a1, hgam]
      simp only [map_mul, map_inv, a2]
    have e2 : (κa * (κ0⁻¹ * κ * κ0)).1 = κa.1 * (κ0.1⁻¹ * κ.1 * κ0.1) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2, map_mul, key, ← map_mul, e1,
      show κ0.1⁻¹ * κ.1⁻¹ * κ0.1 * (κ0.1⁻¹ * κ.1 * κ0.1) = 1 by group, map_one]
  have hc : ((S.K β).lev.chi κa : ℂ) * ((S.K β).lev.chi κ : ℂ) = 1 := by
    have h0 := congrArg (fun w : ℂˣ => (w : ℂ)) ((S.K β).lev.chi_triv _ ht)
    simp only [map_mul, map_inv, Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val] at h0
    have hne : ((S.K β).lev.chi κ0 : ℂ) ≠ 0 := Units.ne_zero _
    field_simp at h0
    linear_combination h0

  have hz : IsTr (atInf (embT D) ((S.loc β).gamI (rep c).1 γ').1) (foTrR (embT D) γ0 y') (foTrR (embT D) γ0 y) := by
    rw [foIsTr_iff, hgam, (foIsTr_iff (embT D) γ y' y).1 hy, ← foTrR_mul, ← foTrR_mul]
    congr 1
    group
  have hE := evC_blk (S.loc β) (tEL D) S.pos (embT D) D.what₂.embLL (tEL_emb D) ((S.loc β).gamI (rep c).1 γ')
    (unit_of_std (S.loc β).B _ Hb.std (Hb.gamU _ γ')) (gramC (gramN D i hi) (embT D)) _ _ hz Q
  rw [hN, Formalism.L2.G.Cmp.map_smul', map_smul, Pi.smul_apply, smul_eq_mul, hr] at hE
  show _ = ((S.K β).lev.chi κ : ℂ) * _
  linear_combination (((S.K β).lev.chi κ : ℂ)) * hE - (evC (Hc S β).P (S.loc β).rk S.pos (gramC (gramN D i hi) (embT D))
    (crdB (embT D) (S.loc β).B) (MvPolynomial.map D.what₂.embLL Q) (foTrR (embT D) γ0 y)) * hc

theorem cmpLiftOf_of_evVal (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) : CmpLiftOf S e :=
  cmpLiftOf_of_raw S e hV (cmpInvRaw_holds S e)

end Rec

section Card

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

end Card

end Formalism.MainNotions.G.CmpJ.PCmpLiftInv
end
end
end
