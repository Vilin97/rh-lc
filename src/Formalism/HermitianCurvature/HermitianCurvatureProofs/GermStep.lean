module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableInvCube
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCSplit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocSupStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBBLiftV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCKer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCBlk
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCStep
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.ImageProdLoc

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem mem_Wb_iff (S : C.HidaSetting E Wp Wq) (m : ℕ) (u : S.W) : u ∈ S.base.Wb m ↔ u ∈ S.base.Wall ∧ S.base.cnt u ≤ m :=
  Finset.mem_filter

theorem Wb_mono (S : C.HidaSetting E Wp Wq) {m m' : ℕ} (h : m ≤ m') : S.base.Wb m ⊆ S.base.Wb m' := by
  intro u hu
  rw [mem_Wb_iff] at hu ⊢
  exact ⟨hu.1, hu.2.trans h⟩

theorem prob_sum_sub {W : Type} {A Wd : Finset W} {θ : W → ℝ} (hθ : TB.IsProb A θ) (h : A ⊆ Wd) :
    ∑ u ∈ Wd, θ u = 1 := by
  rw [← hθ.2.2]
  exact (Finset.sum_subset h fun u _ hu => hθ.2.1 u hu).symm

theorem blockPSD_same {α : Type} (Y : Finset α) (κ : α → α → ℂ) (hκ : TB.PSDOn Y κ) : KB.BlockPSD Y Y κ κ κ := by
  rw [blockPSD_iff]
  have := JCx1.decay.psd_pull Y κ hκ (Y.disjSum Y) (Sum.elim id id) (by
    intro x hx
    rcases x with p | p
    · rw [Finset.inl_mem_disjSum] at hx; exact hx
    · rw [Finset.inr_mem_disjSum] at hx; exact hx)
  refine PBB.psd_congr _ _ _ (fun x hx y hy => ?_) this
  rcases x with p | p <;> rcases y with q | q
  · rfl
  · rfl
  · rw [Finset.inr_mem_disjSum] at hx
    rw [Finset.inl_mem_disjSum] at hy
    simp only [blk, Sum.elim_inl, Sum.elim_inr, id]
    exact psd_herm Y κ hκ hy hx
  · rfl

theorem image_prod_loc {X : Type} (σ : E →+* ℂ) (Y : Finset (TB.Pt E)) (Xs : Finset X) :
    (Y ×ˢ Xs).image (fun p : TB.Pt E × X => (C.loc σ p.1, p.2)) = (Y.image (C.loc σ)) ×ˢ Xs := by
  ext ⟨a, x⟩
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨h, x', ⟨hh, hx'⟩, rfl, rfl⟩; exact ⟨⟨h, hh, rfl⟩, hx'⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩; exact ⟨h, x, ⟨hh, hx⟩, rfl, rfl⟩

theorem germ_global (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (w' : S.W)
    (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = b - 1) :
    ∃ (P Q : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ),
      (∀ v, ∀ h ∈ Y, ∀ h' ∈ Y,
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, z)])
          (C.loc (S.σ v) h' ++ [(n, z)]))) ∧
      GermData Y (fun v p q => KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)])
          (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])) P Q
        (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) := by
  have hloc : ∀ v, ∀ h ∈ Y.image (C.loc (S.σ v)), D.ptSize h = b - 1 := by
    intro v h hh
    obtain ⟨h0, hh0, rfl⟩ := Finset.mem_image.1 hh
    rw [JCx1.needs.ptSize_loc]; exact hY h0 hh0
  have hsup : ∀ v, ∃ B : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ t : ℂ, t ≠ 0 →
      ‖KB.gN S v ε (b + n - 2) (w'.1 v) (h ++ [(n - 1, t)]) (h ++ [(n - 1, t)])‖ ≤ B := by
    intro v
    have hs : ∀ h ∈ Y.image (C.loc (S.σ v)), LocSup S v ε (n - 1) b (w'.1 v) h := by
      intro h hh
      refine locSup_all S hpos hI hg v Λ (hLL v) (hGL v) (fun b s hb hs hbs => hΛ0 b s hb hs hbs v) ε hε (n - 1)
        (by omega) b hb (by omega) h (hloc v h hh) (w'.1 v) ⟨w', rfl⟩ ?_
      have := PBB.len_le_cnt S w' v
      have hk : (n - 1 - 1) * C.Kst ≤ n * C.Kst := Nat.mul_le_mul_right _ (by omega)
      omega
    choose! Bh hBh using hs
    refine ⟨∑ h ∈ Y.image (C.loc (S.σ v)), max (Bh h) 0, fun h hh t ht => ?_⟩
    have := hBh h hh t ht
    rw [show b + (n - 1) - 1 = b + n - 2 by omega] at this
    exact this.trans ((le_max_left _ _).trans (Finset.single_le_sum (f := fun h => max (Bh h) 0)
      (fun _ _ => le_max_right _ _) hh))
  have hG' : ∀ v, ∃ (Pu Pa : C.LPt × ℂ → C.LPt × ℂ → ℂ),
      (∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)),
        ContinuousOn (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)])) {0}ᶜ ∧
        Integrable (fun z => KB.gN S v ε (b + n - 1) (w'.1 v) (h ++ [(n, z)]) (h' ++ [(n, z)]))) ∧
      (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (Y.image (C.loc (S.σ v)) ×ˢ Xs)
        (fun p q => KB.gN S v ε (b + n - 2) (w'.1 v) (p.1 ++ [(n - 1, p.2⁻¹)]) (q.1 ++ [(n - 1, q.2⁻¹)])) Pu Pa) ∧
      (∃ B' : ℝ, ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ x : ℂ, x ≠ 0 → ‖Pa (h, x) (h, x)‖ ≤ B') ∧
      ∀ h ∈ Y.image (C.loc (S.σ v)), ∀ h' ∈ Y.image (C.loc (S.σ v)), ∀ σ : ℂ,
        Tendsto (fun x => Pa (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => Pu (h, x) (h', x + σ)) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) ∧
        Tendsto (fun x => conj (Pu (h', x + σ) (h, x))) (cocompact ℂ) (𝓝 (KB.hatB S v ε b n (w'.1 v) σ h h')) := by
    intro v
    obtain ⟨h1, Pu, Pa, h2, h3, h4⟩ := hGL v ε hε b n hb hn hbn (w'.1 v) ⟨w', rfl⟩ (Y.image (C.loc (S.σ v)))
      (hloc v) (hsup v)
    exact ⟨Pu, Pa, h1, h2, h3, h4⟩
  choose Pu Pa hcont hblk hB' hlim using hG'
  choose Bs hBs using hsup
  choose B' hB'' using hB'
  have mem : ∀ v, ∀ h ∈ Y, C.loc (S.σ v) h ∈ Y.image (C.loc (S.σ v)) := fun v h hh => Finset.mem_image_of_mem _ hh
  refine ⟨fun v p q => Pu v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v p q => Pa v (C.loc (S.σ v) p.1, p.2) (C.loc (S.σ v) q.1, q.2),
    fun v h hh h' hh' => hcont v _ (mem v h hh) _ (mem v h' hh'), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro v Xs hXs
    have := hblk v Xs hXs
    rw [← image_prod_loc (S.σ v) Y Xs] at this
    exact PBB.blockPSD_pull (Y ×ˢ Xs) (fun p : TB.Pt E × ℂ => (C.loc (S.σ v) p.1, p.2)) _ _ _ this
  · refine ⟨∑ v, (max (Bs v) 0 + max (B' v) 0), Finset.sum_nonneg fun v _ => by positivity,
      fun v h hh x hx => ⟨?_, ?_⟩⟩
    · refine ((hBs v _ (mem v h hh) x⁻¹ (inv_ne_zero hx)).trans (le_max_left (Bs v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_right (le_max_right (B' v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
    · refine ((hB'' v _ (mem v h hh) x hx).trans (le_max_left (B' v) 0)).trans ?_
      refine le_trans (le_add_of_nonneg_left (le_max_right (Bs v) 0)) ?_
      exact Finset.single_le_sum (f := fun v => max (Bs v) 0 + max (B' v) 0) (fun _ _ => by positivity)
        (Finset.mem_univ v)
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.1
  · intro v h hh h' hh' σ; exact (hlim v _ (mem v h hh) _ (mem v h' hh') σ).2.2

end

end Formalism.FourierDecayAlt.P.PBC
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.GermStep

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem germ_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (w' : S.W) (hw' : w' ∈ S.base.Wall) (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop)
    (La : Submodule ℤ (crystallineComparison.V S.f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (hsm : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (z₀ : crystallineComparison.V S.f) (Ss : Finset (crystallineComparison.V S.f)), (∀ z ∈ Ss, z - z₀ ∈ La) → (∀ z ∈ Ss, Good z) →
          ZLattice.covolume La * ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re ≤
            (∏ _v : Fin S.f, KB.dlB S b n) *
              ((∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) * P') *
              ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ := by
  have hk : n * C.Kst = (n - 1) * C.Kst + C.Kst := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [add_mul, one_mul]
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef
  have hL0 : ∀ v, 0 ≤ L v := fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v

  obtain ⟨θL, hθL, hLV⟩ := Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega)
    (by omega) (by omega) w' hw' (by omega)
  have hΛi : b + n - 2 - (n - 1) + 1 = b := by omega
  rw [hΛi] at hLV

  choose! θ'' hθ'' using hP'
  set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd
  set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs
  have hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧
      (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd) := by
    intro x hx
    rw [hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff] at hx
    exact ⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩
  have hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop →
      TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u) := fun u h1 h2 => (hθ'' u h1 h2).1
  let q : crystallineComparison.V S.f → S.W → ℝ := fun σ u =>
    ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)
  have hq : ∀ σ, TB.IsProb Wd (q σ) := by
    intro σ
    set A := crystallineComparison.pat L ((S.g : ℝ) • σ)
    refine ⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg
      ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)),
      fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩
    · have h1 : θ'' x.1 u = 0 := (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)
      have h2 : θ'' x.2 u = 0 := (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)
      simp [h1, h2]
    · show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1
      rw [Finset.sum_comm, ← (hθL A).2.2]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2,
        prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]
      norm_num
  obtain ⟨θn, hθn, hmix⟩ := tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm
    (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)
  refine ⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩
  obtain ⟨Pq, Qq, hreg, hGD⟩ := germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'
  have := j1; have := j2
  set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  let U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ := fun v p q =>
    KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])
  have hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t →
      (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧
      (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u := by
    intro x' hx' t ht
    have e : b + (n - 1) - 1 = b + n - 2 := by omega
    have h1 := (hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht
    have h2 := (hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht
    rw [e] at h1 h2
    have s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    have s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    exact ⟨s1 ▸ h1, s2 ▸ h2⟩
  have hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤
        crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u := by
    intro σ _ x hx hx'
    set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def
    set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def
    have ht : Good t := fun v => inv_ne_zero (hx v)
    have ht' : Good t' := fun v => inv_ne_zero (hx' v)
    have ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t' := by
      rw [nstV_eq]; rfl
    have hlv := hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht'
      (crystallineComparison.pat L ((S.g : ℝ) • σ))
    have ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v) := by
      intro v; simp only [t, t', inv_inv, Pi.add_apply]; ring
    simp only [ediff, norm_neg] at hlv
    rw [ephi]
    refine bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)
    show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x' hx' => ?_
    have hs := hsub x' hx'
    have e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u =
        θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')
    linarith [(hs t ht).1, (hs t' ht').2]
  have hH := herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n)
    (fun _ => dlB_pos S hg b n) U Pq Qq
    (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) hGD
    (fun _ _ _ _ => rfl) La Lm hLm
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u) (hmix N').1 hF z₀ Ss hS
  rw [(hmix N').2] at hH
  have hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re :=
    Finset.sum_congr rfl fun z hz => by
      simp only [Nz, if_pos (hgood z hz)]
      rw [nstV_eq]
      rfl
  rw [hN] at hH
  refine hH.trans (le_of_eq ?_)
  have e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
  rw [e3]
  ring

end

end Formalism.FourierDecayAlt.P.PBC
end
end
