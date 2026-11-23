module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetMaxAtGoodEmb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

-- Source module: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.EqZeroOfPnorm

section

@[expose] public section

noncomputable section

namespace GlobalTheory.NetNormExamples

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg X la x)

theorem pnorm_le_supN (U : Unf Xo c σ r) (la) {P : FDSec U.X} (hP : P ∈ holSub U.X la) (p : FPt U.X) :
    (U.X p.1).pnorm (la p.1) (P p.1) p.2 ≤ supN U.X la P := by
  unfold supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem eq_zero_of_pnorm (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h0 : X.pnorm la P x = 0) : P x = 0 := by
  have hne : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i e => by
    have := (hx τ).2 i
    rw [e] at this; simp at this
  unfold Data.pnorm at h0
  refine norm_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (ne_of_gt ?_))
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))) _

end GlobalTheory.NetNormExamples
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetDataFromHalfConjugateEmbeddings

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.NetNorms
open scoped ComplexConjugate

namespace GlobalTheory

theorem linearIndependent_conj_coords {ι κ : Type*} [Fintype ι] (v : ι → κ → ℂ)
    (h : LinearIndependent ℂ v) : LinearIndependent ℂ (fun i y => conj (v i y)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc i
  have h1 : ∑ i, conj (c i) • v i = 0 := by
    funext y
    have := congrArg conj (congrFun hc y)

    simpa [Finset.sum_apply, map_sum] using this
  simpa using h (fun i => conj (c i)) h1 i

theorem exists_netData_of_readings_on_half :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (good : (B.KO →+* ℂ) → Prop), (∀ σ, good σ ↔ ¬ good (ComplexEmbedding.conjugate σ)) → (∀ σ F, B.supN j ka (ComplexEmbedding.conjugate σ) F = B.supN j ka σ F) → ∀ (n : (B.KO →+* ℂ) → ℕ) (ev : ∀ σ, Fin (n σ) → (B.Cusp j ka →ₛₗ[σ] ℂ)) (C : ℝ), (∀ σ, good σ → (∀ F, ∃ y, B.supN j ka σ F / 4 ≤ ‖ev σ y F‖) ∧ (∀ y F, ‖ev σ y F‖ ≤ B.supN j ka σ F) ∧ Real.log (16 * (n σ : ℝ)) ≤ C ∧ ∀ (m : ℕ) (F : Fin m → B.Cusp j ka), LinearIndependent B.KO F → LinearIndependent ℂ (fun i => fun y => ev σ y (F i))) → ∃ Nt : NetData B j ka, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt C ∧ ∀ σ, NetInj Nt σ := by
  classical
  intro D B j ka good hgood hsup n ev C H
  have cc : ∀ σ : B.KO →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ := by
    intro σ
    ext a
    simp
  let g : (B.KO →+* ℂ) → (B.KO →+* ℂ) := fun σ => if good σ then σ else ComplexEmbedding.conjugate σ
  have hgc : ∀ σ, ¬ good σ → good (ComplexEmbedding.conjugate σ) := by
    intro σ h
    by_contra h'
    exact h ((hgood σ).2 h')
  have g1 : ∀ σ, good σ → g σ = σ := fun σ h => if_pos h
  have g2 : ∀ σ, ¬ good σ → g σ = ComplexEmbedding.conjugate σ := fun σ h => if_neg h
  have gg : ∀ σ, good (g σ) := by
    intro σ
    by_cases h : good σ
    · rw [g1 σ h]; exact h
    · rw [g2 σ h]; exact hgc σ h
  have gc : ∀ σ, g σ = g (ComplexEmbedding.conjugate σ) := by
    intro σ
    by_cases h : good σ
    · rw [g1 σ h, g2 _ ((hgood σ).1 h), cc]
    · rw [g2 σ h, g1 _ (hgc σ h)]
  have gs : ∀ σ F, B.supN j ka (g σ) F = B.supN j ka σ F := by
    intro σ F
    by_cases h : good σ
    · rw [g1 σ h]
    · rw [g2 σ h, hsup]
  have hcast : ∀ (a b : B.KO →+* ℂ) (h : a = b) (y : Fin (n a)) (F : B.Cusp j ka),
      ev b (finCongr (congrArg n h) y) F = ev a y F := by
    intro a b h y F
    subst h
    rfl
  let ev' : ∀ σ, Fin (n (g σ)) → (B.Cusp j ka →ₛₗ[σ] ℂ) := fun σ y =>
    { toFun := fun F => if good σ then ev (g σ) y F else conj (ev (g σ) y F)
      map_add' := by
        intro F G
        split_ifs <;> simp
      map_smul' := by
        intro a F
        by_cases h : good σ
        · have e : g σ a = σ a := by rw [g1 σ h]
          simp only [if_pos h, map_smulₛₗ, e]
        · have e : g σ a = conj (σ a) := by rw [g2 σ h]; rfl
          simp [if_neg h, map_smulₛₗ, e] }
  have e1 : ∀ σ y F, good σ → ev' σ y F = ev (g σ) y F := fun σ y F h => if_pos h
  have e2 : ∀ σ y F, ¬ good σ → ev' σ y F = conj (ev (g σ) y F) := fun σ y F h => if_neg h
  have en : ∀ σ y F, ‖ev' σ y F‖ = ‖ev (g σ) y F‖ := by
    intro σ y F
    by_cases h : good σ
    · rw [e1 σ y F h]
    · rw [e2 σ y F h, Complex.norm_conj]
  refine ⟨{ NN := fun σ => Fin (n (g σ))
            ev := ev'
            cj := fun σ => finCongr (congrArg n (gc σ))
            ev_conj := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro σ y F
    by_cases h : good σ
    · rw [e2 _ _ _ ((hgood σ).1 h), e1 _ _ _ h, hcast _ _ (gc σ)]
    · rw [e1 _ _ _ (hgc σ h), e2 _ _ _ h, hcast _ _ (gc σ), Complex.conj_conj]
  · intro σ F
    obtain ⟨y, hy⟩ := (H _ (gg σ)).1 F
    refine ⟨y, ?_⟩
    show _ ≤ ‖ev' σ y F‖
    rw [en, ← gs]
    exact hy
  · intro σ y F
    show ‖ev' σ y F‖ ≤ _
    rw [en, ← gs]
    exact (H _ (gg σ)).2.1 y F
  · intro σ
    show Real.log (16 * (Fintype.card (Fin (n (g σ))) : ℝ)) ≤ C
    rw [Fintype.card_fin]
    exact (H _ (gg σ)).2.2.1
  · intro σ m F hF
    have hI := (H _ (gg σ)).2.2.2 m F hF
    show LinearIndependent ℂ (fun i => fun y : Fin (n (g σ)) => ev' σ y (F i))
    by_cases h : good σ
    · simp only [e1 σ _ _ h]
      exact hI
    · simp only [e2 σ _ _ h]
      exact linearIndependent_conj_coords _ hI

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetDataFromHalfConjugateEmbeddingsStatement

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.NetNorms

theorem _root_.GlobalTheory.T.exists_netData_from_half_conjugate_embeddings : ∀ (D : D7) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (good : (B.KO →+* ℂ) → Prop), (∀ σ, good σ ↔ ¬ good (ComplexEmbedding.conjugate σ)) → (∀ σ F, B.supN j ka (ComplexEmbedding.conjugate σ) F = B.supN j ka σ F) → ∀ (n : (B.KO →+* ℂ) → ℕ) (ev : ∀ σ, Fin (n σ) → (B.Cusp j ka →ₛₗ[σ] ℂ)) (C : ℝ), (∀ σ, good σ → (∀ F, ∃ y, B.supN j ka σ F / 4 ≤ ‖ev σ y F‖) ∧ (∀ y F, ‖ev σ y F‖ ≤ B.supN j ka σ F) ∧ Real.log (16 * (n σ : ℝ)) ≤ C ∧ ∀ (m : ℕ) (F : Fin m → B.Cusp j ka), LinearIndependent B.KO F → LinearIndependent ℂ (fun i => fun y => ev σ y (F i))) → ∃ Nt : NetData B j ka, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt C ∧ ∀ σ, NetInj Nt σ := by
  first | exact @GlobalTheory.exists_netData_of_readings_on_half | exact GlobalTheory.exists_netData_of_readings_on_half | (intros; apply GlobalTheory.exists_netData_of_readings_on_half <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetDataExists

section

@[expose] public section

open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn.NetAtRecord

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem good_conj_iff (c : Coeff l) (σ : c.F →+* ℂ) :
    GoodEmb c (ComplexEmbedding.conjugate σ) ↔ ¬ GoodEmb c σ := by
  constructor
  · intro h1 h2
    have e : (starRingEnd ℂ) H.rt0 = H.rt0 := by
      have h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h1
      rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2] at h3
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp e
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  · intro h
    have := goodEmb_goodOf c σ
    unfold goodOf at this
    rwa [if_neg h] at this

theorem goodOf_conj (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (ComplexEmbedding.conjugate σ) = goodOf c σ := by
  unfold goodOf
  by_cases h : GoodEmb c σ
  · rw [if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]
    ext x; simp [ComplexEmbedding.conjugate]
  · rw [if_pos ((good_conj_iff c σ).2 h), if_neg h]; rfl

end

theorem supN_conj {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (F : (recB h.toLawsCore).Cusp j w) :
    (recB h.toLawsCore).supN j w (ComplexEmbedding.conjugate σ) F = (recB h.toLawsCore).supN j w σ F := by
  have e : T.Ns j w (ComplexEmbedding.conjugate σ) = T.Ns j w σ := by
    funext f
    unfold Core.Ns
    rw [goodOf_conj]
  change cutN T.C T.Ns j w (ComplexEmbedding.conjugate σ) F = cutN T.C T.Ns j w σ F
  unfold cutN
  rw [e]

theorem netData_exists : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∃ Nt : NetData (recB h.toLawsCore) j w, NetMax Nt ∧ NetLeSup Nt ∧ NetSize Nt (1041 * Zb D large₂ ^ 3) ∧ ∀ σ, NetInj Nt σ := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro D T h hG large₂ j hj w hP hL hr hf
    classical
    have key : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F → LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
      intro D T h hG large₂ j hj w hP hL hr hf σ hσ
      classical
      obtain ⟨NN, -, hnet, hlog⟩ :=
        GlobalTheory.RunIn.exists_net_max_at_goodEmb D T h hG large₂ j hj w hP hL hr hf σ hσ
      obtain ⟨L, hLdef⟩ : ∃ L, L = lieFac (T.Q.Dw j) (xiR D) (wtA w) := ⟨_, rfl⟩
      have hL0 : 0 < L := hLdef ▸ lieFac_pos _ _ _

      have hpn : ∀ (k : (T.U j σ).Comp) (P : Frame ((T.U j σ).X k).Ψ D.R.r → ℂ) x,
          ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) P x
            = ‖P x‖ * ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := fun _ _ _ => rfl
      have hnf : ∀ (k : (T.U j σ).Comp) x, 0 ≤ ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := by
        intro k x
        have h1 := GlobalTheory.NetNormExamples.pnorm_nonneg ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
          (fun _ => (1 : ℂ)) x
        rwa [hpn, norm_one, one_mul] at h1
      have hg : goodOf T.Q.c σ = σ := by rw [goodOf, ite_eq_left hσ]

      have hsup : ∀ F : (recB h.toLawsCore).Cusp j w, (recB h.toLawsCore).supN j w σ F =
          L * supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) F.1) := by
        intro F
        dsimp only [recB, cutN]
        rw [ite_eq_left hj]
        dsimp only [Formalism.L2.Pj.Core.Ns, supC]
        rw [hg, hLdef]

      have hC (F : (recB h.toLawsCore).Cusp j w) :
          F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (Submodule.mem_inf.mp F.2).1
      have hhol : ∀ F : (recB h.toLawsCore).Cusp j w,
          rdU (T.U j σ) F.1 ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
        intro F
        exact ((mem_cusp _ _ _ _ _ _).mp (hC F)).2 σ hσ

      let pt : Fin NN.card → FPt (T.U j σ).X := fun y => (NN.equivFin.symm y).1
      have hsurj : ∀ p ∈ NN, ∃ y, pt y = p := fun p hp =>
        ⟨NN.equivFin ⟨p, hp⟩, by simp only [pt, Equiv.symm_apply_apply]⟩
      let a : Fin NN.card → ℝ := fun y =>
        L * ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2
      have ha : ∀ y, 0 ≤ a y := fun y => mul_nonneg hL0.le (hnf _ _)

      let ev : Fin NN.card → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ) := fun y =>
        { toFun := fun F => (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2
          map_add' := fun F G => by
            show (a y : ℂ) * rdU (T.U j σ) (F.1 + G.1) (pt y).1 (pt y).2 =
              (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 + (a y : ℂ) * rdU (T.U j σ) G.1 (pt y).1 (pt y).2
            rw [map_add (f := _), Pi.add_apply, Pi.add_apply, mul_add]
          map_smul' := fun c F => by
            show (a y : ℂ) * rdU (T.U j σ) (c • F.1) (pt y).1 (pt y).2 =
              σ c • ((a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2)
            rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
            ring }
      have hev : ∀ y F, ev y F = (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 := fun _ _ => rfl
      have hnorm : ∀ y F, ‖ev y F‖ =
          L * ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1)
            (rdU (T.U j σ) F.1 (pt y).1) (pt y).2 := by
        intro y F
        rw [hev, norm_mul, Complex.norm_of_nonneg (ha y), hpn]
        simp only [a]
        ring
      refine ⟨NN.card, ev, ?_, ?_, ?_, ?_⟩
      · intro F
        obtain ⟨p, hp, hb⟩ := hnet _ (hhol F)
        obtain ⟨y, rfl⟩ := hsurj p hp
        refine ⟨y, ?_⟩
        rw [hnorm, hsup]
        have := mul_le_mul_of_nonneg_left hb hL0.le
        linarith
      · intro y F
        rw [hnorm, hsup]
        exact mul_le_mul_of_nonneg_left
          (GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ (hhol F) (pt y)) hL0.le
      · exact hlog
      · intro m F hF
        have hlin := hF.map' (cutR T.C j w).subtype (cutR T.C j w).ker_subtype
        have hmem : ∀ i, (F i).1 ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := fun i =>
          Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n (hC (F i))
        have hU := h.unf j hj σ hσ
        have hB := GlobalTheory.lawsFieldsSeparately.2.1
        have hreading := (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (T.Q.Xo j) T.Q.c σ _
          (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 hU)
          (wtA w) w.n).1 m (fun i => (F i).1) hmem hlin
        have hind : LinearIndependent ℂ (fun i => rdU (T.U j σ) (F i).1) := by
          exact hreading
        rw [Fintype.linearIndependent_iff] at hind ⊢
        intro g hgz i
        refine hind g ?_ i
        show ∑ i, g i • rdU (T.U j σ) (F i).1 = 0
        obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i, g i • rdU (T.U j σ) (F i).1 := ⟨_, rfl⟩
        rw [← hQ]
        have hQmem : Q ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
          rw [hQ]
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hhol (F i))
        have hval : ∀ y, (a y : ℂ) * Q (pt y).1 (pt y).2 = 0 := by
          intro y
          have h1 := congrFun hgz y
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hev] at h1
          rw [hQ, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, ← h1]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring
        obtain ⟨p, hp, hb⟩ := hnet Q hQmem
        obtain ⟨y, rfl⟩ := hsurj p hp
        have h0 : ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1) (Q (pt y).1) (pt y).2 = 0 := by
          have hn := congrArg (‖·‖) (hval y)
          simp only [norm_mul, Complex.norm_of_nonneg (ha y), norm_zero] at hn
          simp only [a] at hn
          rw [hpn]
          have h2 : L * (‖Q (pt y).1 (pt y).2‖ *
              ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2) = 0 := by
            rw [← hn]; ring
          exact (mul_eq_zero.mp h2).resolve_left hL0.ne'
        have hS : supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) Q ≤ 0 := by
          rw [h0, mul_zero] at hb
          exact hb
        funext k x
        by_cases hx : x ∈ ((T.U j σ).X k).dom
        · show Q k x = 0
          apply GlobalTheory.NetNormExamples.eq_zero_of_pnorm ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) _ hx
          exact le_antisymm
            ((GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ hQmem ⟨k, ⟨x, hx⟩⟩).trans hS)
            (GlobalTheory.NetNormExamples.pnorm_nonneg _ _ _ _)
        · show Q k x = 0
          rw [hQ, Finset.sum_apply, Finset.sum_apply]
          refine Finset.sum_eq_zero fun i _ => ?_
          have hz : rdU (T.U j σ) (F i).1 k x = 0 := by
            simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hx]
          rw [Pi.smul_apply, Pi.smul_apply, hz, smul_zero]
    have key := key D T h hG large₂ j hj w hP hL hr hf
    have key2 : ∀ σ : T.Q.c.F →+* ℂ, ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)),
        GoodEmb T.Q.c σ → (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧
          (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧
          ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F →
            LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
      intro σ
      by_cases hσ : GoodEmb T.Q.c σ
      · obtain ⟨n, ev, H⟩ := key σ hσ
        exact ⟨n, ev, fun _ => H⟩
      · exact ⟨0, Fin.elim0, fun h' => absurd h' hσ⟩
    choose n ev H using key2
    exact GlobalTheory.T.exists_netData_from_half_conjugate_embeddings D (recB h.toLawsCore) j w (GoodEmb T.Q.c)
      (fun σ => by rw [good_conj_iff]; exact not_not.symm) (supN_conj h j w) n ev _ H

end GlobalTheory.RunIn.NetAtRecord
end
end
