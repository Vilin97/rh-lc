module

public import Formalism.HermitianCurvature.ArchimedeanUniformConstantsCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralFormulaPassesToLimits
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfLocal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalNormNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBCutInside
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBJoint
public import Formalism.HermitianCurvature.StatementKB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OutsideSystemsBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SizeAtNonneg
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.TopOfLocal

section

@[expose] public section

open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

theorem top_of_local : KB.TopOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ' hpos _ hloc ε hε s hs2 hsr w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v =>
    le_trans (Nat.add_le_add_right (len_le_cnt S w.1 v) _) hcnt'
  choose U θ hUθ using fun v => hloc v s hs2 hsr (w.1 v) ⟨w, rfl⟩ (hlen v)
  have hU : ∀ v, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hUθ v).1.2 a ha).1,
      le_trans ((hUθ v).1.2 a ha).2 (Nat.add_le_add_right (len_le_cnt S w.1 v) _)⟩
  have hw : w.1.cnt ≤ w.1.cnt + C.Kst := Nat.le_add_right _ _
  refine ⟨fun B => pθ S B w θ, fun B => pθ_prob (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt', ?_⟩
  intro Y hY κ hκ t ht B
  let g : Fin S.f → TB.Pt E → C.LPt := fun v h => C.loc (S.σ v) h ++ [(s, S.σ v t)]
  let G : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.gN S v ε (S.G.r + 1) (w.1 v) (g v h) (g v h')
  let M : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    KB.mix S v ε (S.G.r + 1) (U v) (θ v) (g v h) (g v h')
  let c : Fin S.f → ℝ := fun v => (‖S.σ v t‖ * Λ' (S.G.r + 2 - s) s v) ^ (2 * C.Kst)
  let A : Fin S.f → TB.Pt E → TB.Pt E → ℂ := fun v h h' =>
    if v ∈ B then (c v : ℂ) * M v h h' else G v h h'
  have hG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (G v) := fun v _ =>
    psd_comp _ _ (gN_psd S hpos v hε le_rfl w (Y.image (g v))) Y (g v)
      (fun h hh => mem_image_of_mem _ hh)
  have hAG : ∀ v ∈ (univ : Finset (Fin S.f)), TB.PSDOn Y (fun x y => A v x y - G v x y) := by
    intro v _
    by_cases hv : v ∈ B
    · have hσ : S.σ v t ≠ 0 := (map_ne_zero (S.σ v)).mpr ht
      have hY' : ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = S.G.r + 1 - s := by
        intro p hp
        obtain ⟨h, hh, rfl⟩ := mem_image.mp hp
        rw [ptSize_loc]
        exact hY h hh
      have h1 := psd_comp _ _ ((hUθ v).2 ε hε (S.σ v t) _ hσ hY') Y (C.loc (S.σ v))
        (fun h hh => mem_image_of_mem _ hh)
      refine Jx8.psd_congr ?_ h1
      intro x _ y _
      simp only [A, if_pos hv]
      rfl
    · refine Jx8.psd_congr ?_ (Jx8.zero_psd Y)
      intro x _ y _
      simp only [A, if_neg hv, sub_self]
  have hle := BaseGramNonnegativity.sum_re_nonneg Y κ _ hκ (Jx7.psd_prod_dom univ G A hG hAG)
  have hprod : ∀ h h', ∏ v, A v h h' =
      (∏ v ∈ B, (c v : ℂ)) * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    intro h h'
    calc ∏ v, A v h h'
        = ∏ v, ((if v ∈ B then (c v : ℂ) else 1) * (if v ∈ B then M v h h' else G v h h')) :=
          prod_congr rfl (fun v _ => by by_cases hv : v ∈ B <;> simp [A, hv])
      _ = (∏ v, (if v ∈ B then (c v : ℂ) else 1)) * ∏ v, (if v ∈ B then M v h h' else G v h h') :=
          prod_mul_distrib
      _ = _ := by rw [prod_ite_mem, univ_inter]
  have hexp : ∀ h h', ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h') =
      ∏ v, (if v ∈ B then M v h h' else G v h h') := fun h h' =>
    expand (fun v _ => (hUθ v).1.1) (fun v _ => hU v) hw hcnt'
      (fun v a => KB.gN S v ε (S.G.r + 1) a (g v h) (g v h'))
  have hR : ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') := by
    simp only [Nst_eq S (i := S.G.r + 1) le_rfl]
    have hm := mix_sum Y (S.base.Wb (w.1.cnt + C.Kst)) κ 1 (fun w' => (pθ S B w θ w' : ℂ))
      (fun w' h h' => ∏ v, KB.gN S v ε (S.G.r + 1) (w'.1 v) (g v h) (g v h'))
    simp only [one_mul] at hm
    rw [← hm]
    refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
    rw [hexp h h']
  have hC : ∏ v ∈ B, (S.base.av v t * Λ' (S.G.r + 2 - s) s v) ^ (2 * S.base.K) = ∏ v ∈ B, c v :=
    prod_congr rfl fun v _ => by rw [av_eq]; rfl
  have hsum : ∑ w' ∈ S.base.Wb (S.base.cnt w + S.base.K),
        pθ S B w θ w' * (S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re =
      (∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S B w θ w' : ℂ) *
        S.base.Nst ε (S.G.r + 1) s w' Y κ t t).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun w' _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [hC, hsum, hR, Nst_eq S (i := S.G.r + 1) le_rfl s w Y κ t t, ← Complex.re_ofReal_mul,
    Complex.ofReal_prod]
  have hA : (∏ v ∈ B, (c v : ℂ)) * ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (if v ∈ B then M v h h' else G v h h') =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, A v h h' := by
    rw [mul_sum]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun h' _ => ?_
    rw [hprod h h', mul_left_comm]
  rw [hA]
  simp only [mul_sub, sum_sub_distrib, Complex.sub_re] at hle
  linarith

end

end Formalism.FourierDecayAlt.P.PBA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def cutN {k r : ℕ} (n : ℕ) (g : B.Mat k r) : ℂ :=
  ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def cutSeq (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (n : ℕ) :
    ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  fun v ε g => cutN n g • D.cutF (p v).T.base χ (f v) ε g

end defs

def WaveLocB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (PBL.setC S p F) v fun i => X i v

def LiftLocB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ, (∀ b s v, 0 ≤ Λ b s v) ∧
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (PBL.setC S p F) v fun b s => Λ b s v

def GermLocB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n v, KB.GermLoc (PBL.setC S p (cutSeq S p f χ n)) v

def PosB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → C.ThmPPos (PBL.setC S p F)

def DecayUnif : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 → ∃ C : ℝ, ∀ n, (∀ c : ℂ, c ≠ 0 →
        ‖(PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤
          C * ((1 + ‖c‖) ^ 3)⁻¹) ∧
        ∀ l : ℂ, ‖∫ c : ℂ, (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)]) *
          KB.psiL S l c‖ ≤ C * ((1 + ‖l‖) ^ 3)⁻¹

def IntB : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n, KB.IntAll (PBL.setC S p (cutSeq S p f χ n))

def ThresholdsPositive : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ b s v, 1 ≤ b → 1 ≤ s → 0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v)

theorem psd_of_tendsto {α : Type} (Y : Finset α) (k : ℕ → α → α → ℂ) (k0 : α → α → ℂ)
    (hk : ∀ n, TB.PSDOn Y (k n)) (hl : ∀ x y, Tendsto (fun n => k n x y) atTop (𝓝 (k0 x y))) :
    TB.PSDOn Y k0 := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun x _ y _ => ?_, fun c => ?_⟩
  · have h1 : Tendsto (fun n => k n y x) atTop (𝓝 (conj (k0 x y))) := by
      have := ((Complex.continuous_conj.tendsto _).comp (hl x y))
      refine this.congr fun n => ?_
      exact (((PBA.psd_iff_qf Y (k n)).1 (hk n)).1 x ‹_› y ‹_›).symm
    exact tendsto_nhds_unique (hl y x) h1
  · have hq : Tendsto (fun n => (PBA.qf Y (k n) c).re) atTop (𝓝 (PBA.qf Y k0 c).re) := by
      refine (Complex.continuous_re.tendsto _).comp ?_
      unfold PBA.qf
      refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
      exact ((tendsto_const_nhds.mul (hl x y)).mul tendsto_const_nhds)
    exact ge_of_tendsto' hq fun n => (((PBA.psd_iff_qf Y (k n)).1 (hk n)).2 c)

theorem core (hW : WaveLocB) (hL : LiftLocB) (hTL : PBL.TopLocB) (hDT : KB.DegTop) (hVT : Top.VecVTypes)
    (hTR : PBL.TopRatio) (hG : GermLocB) (hP : PosB) (hI : IntB) (hD : DecayUnif) (hTh : ThresholdsPositive) (Cb : ℝ) :
    ∃ Cc C₄ : ℝ, 1 ≤ C₄ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
      [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
      [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
      [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
      (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
      (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
      KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
        C.ThmPPos S ∧ KB.IntAll S ∧ (∃ Lw, JC.WaveByPlaces S Lw ∧ JC.HidaCurvatureBarriers S Lw) ∧
        (∃ Ll Ll', JC.LiftBelowTop S Ll ∧ JC.LiftTopDiag S Ll' ∧ JC.ThresholdsLift S Ll Ll') ∧
        JC.SumFormConcrete S C₄ := by
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  obtain ⟨C₄, hC₄, hSF⟩ := sum_form_of_local_statements
  obtain ⟨c2, h2⟩ := hW Cb
  obtain ⟨c3, h3⟩ := hL Cb
  obtain ⟨c4, h4⟩ := hG Cb
  obtain ⟨c5, h5⟩ := hP Cb
  obtain ⟨c6, h6⟩ := hI Cb
  obtain ⟨c7, h7⟩ := hD Cb
  obtain ⟨c8, h8⟩ := hTh Cb
  set Cc : ℝ := max (max (max c1 c2) (max c3 c4)) (max (max c5 c6) (max c7 (max c8 (28 * Real.exp 1)))) with hCc
  refine ⟨Cc, C₄, hC₄, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB
  have le1 : c1 ≤ Cc := by simp [hCc]
  have le2 : c2 ≤ Cc := by simp [hCc]
  have le3 : c3 ≤ Cc := by simp [hCc]
  have le4 : c4 ≤ Cc := by simp [hCc]
  have le5 : c5 ≤ Cc := by simp [hCc]
  have le6 : c6 ≤ Cc := by simp [hCc]
  have le7 : c7 ≤ Cc := by simp [hCc]
  have le8 : c8 ≤ Cc := by simp [hCc]
  have le9 : 28 * Real.exp 1 ≤ Cc := by simp [hCc]
  have hB' := hB
  obtain ⟨hg1, hg2, hU, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB

  have hFL : ∀ v ε, 0 < ε → (∀ n, KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε)) ∧
      ∀ i w, KB.CutWord (D.parOf S v) (p v).l0 w → w.length ≤ S.Ntop → ∀ a b,
        Tendsto (fun n => (p v).RR (cutSeq S p f χ n v ε) i w a b) atTop
          (𝓝 ((p v).RR (D.cutF (p v).T.base χ (f v) ε) i w a b)) := by
    intro v ε hε
    obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
    refine h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop cutN (by rw [hl0]; exact hInD)
      hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right le1 (by positivity)) (by positivity)
  have hcpt : ∀ n v ε, 0 < ε → KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε) := fun n v ε hε => (hFL v ε hε).1 n
  have hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ P Q,
      Tendsto (fun n => PBL.rrC S p (cutSeq S p f χ n) v ε i a P Q) atTop (𝓝 ((S.pd v).RR ε i a P Q)) := by
    intro v ε hε i a ha P Q
    obtain ⟨hl0, -, hpd, -, -⟩ := hv v
    obtain ⟨w, rfl⟩ := ha
    have hcw : KB.CutWord (D.parOf S v) (p v).l0 (w.1 v) := by rw [hl0]; exact PBD.cutWord_of_adm S hGo hCI w v
    have hlen : (w.1 v).length ≤ S.Ntop := le_trans (PBB.len_le_cnt S w v) w.2.2
    have ht := ((hFL v ε hε).2 i (w.1 v) hcw hlen (D.toStd S.G.r (S.g : ℝ) 1 P) (D.toStd S.G.r (S.g : ℝ) 1 Q)).const_mul
      (((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P * D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
        D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ))
    have hval : (S.pd v).RR ε i (w.1 v) P Q = (((1 / (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P *
        D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) Q *
        D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i) : ℝ) : ℂ)) *
        (p v).RR (D.cutF (p v).T.base χ (f v) ε) i (w.1 v) (D.toStd S.G.r (S.g : ℝ) 1 P)
          (D.toStd S.G.r (S.g : ℝ) 1 Q) := by
      rw [hpd]
      simp only [D.componentFamilySetting_ofSetting, KB.Pl.RR, hl0, one_pow]
    rw [hval]
    exact ht

  set RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ := fun n => PBL.rrC S p (cutSeq S p f χ n)
    with hRR
  have hIn : ∀ n, KB.IntAll (KB.withRR S (RR n)) := h6 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le6 hB)
  have hPn : ∀ n, C.ThmPPos (KB.withRR S (RR n)) := fun n =>
    h5 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le5 hB) _ (hcpt n)
  obtain ⟨hIS, hWL⟩ := integral_formula_passes_to_limits E Wp Wq S RR hg1 hg2 hU hconv hIn
    (h7 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le7 hB))
  obtain ⟨hLC1, hLC2, hLC3⟩ := PBA.limit_closed E Wp Wq S RR hconv
  obtain ⟨X0, hXt0, hXl0⟩ := h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le2 hB)

  set X : ℕ → Fin S.f → ℝ := fun i v => if 1 ≤ i ∧ i ≤ S.G.r + 1 then X0 i v else 0 with hXdef
  have hX0 : ∀ i v, 0 ≤ X i v := by
    intro i v
    by_cases hi : 1 ≤ i ∧ i ≤ S.G.r + 1
    · simp only [hXdef, if_pos hi]; exact (hXt0 i hi.1 hi.2 v).1
    · simp only [hXdef, if_neg hi, le_refl]
  have hXt : JC.HidaCurvatureBarriers S X := by
    intro i hi1 hi2 v
    simp only [hXdef, if_pos (And.intro hi1 hi2)]
    exact hXt0 i hi1 hi2 v
  have hXl : ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (PBL.setC S p F) v fun i => X i v := by
    intro F hF v i hi1 hi2
    have hXi : X i v = X0 i v := by rw [hXdef]; exact if_pos ⟨hi1, hi2⟩
    simp only [hXi]
    exact hXl0 F hF v i hi1 hi2
  obtain ⟨Λ, hΛ0, hΛs, hΛl⟩ := h3 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le3 hB)
  obtain ⟨hTt, hTl⟩ := hTL hDT hVT hTR Cb Cc E Wp Wq S p f χ A₀ le9 hB
  have hGL := h4 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le4 hB)
  have hthr := h8 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place le8 hB)
  have hWn : ∀ n, JC.WaveByPlaces (KB.withRR S (RR n)) X := fun n =>
    plane_wave_bound_of_local_bounds E Wp Wq (KB.withRR S (RR n)) X hg1 hg2 hU hGo (hIn n) hX0 (hXl _ (hcpt n))
  have hLn : ∀ n, JC.LiftBelowTop (KB.withRR S (RR n)) Λ := fun n =>
    PBA.liftOfLoc_statement E Wp Wq (KB.withRR S (RR n)) Λ (hPn n) hGo hΛ0 (hΛl _ (hcpt n))
  have hTn : ∀ n, JC.LiftTopDiag (KB.withRR S (RR n)) (fun b _ v => PBL.lamTop S b v) := fun n =>
    PBA.top_of_local E Wp Wq (KB.withRR S (RR n)) _ (hPn n) hGo (hTl _ (hcpt n))
  have hSn : ∀ n, JC.SumFormConcrete (KB.withRR S (RR n)) C₄ := fun n =>
    hSF E Wp Wq (KB.withRR S (RR n)) X Λ hg1 hg2 hU (hPn n) hGo (hIn n) (hXl _ (hcpt n)) hXt (hΛl _ (hcpt n))
      (fun b s hb hs hbs v => ⟨hΛ0 b s v, hΛs b s hb hs hbs v⟩) hthr (hGL n)

  have hpos : C.ThmPPos S := by
    intro v ε hε i hi w Y
    refine psd_of_tendsto Y (fun n => (KB.withRR S (RR n)).gramLoc v ε i (w.1 v)) _ (fun n => hPn n v ε hε i hi w Y)
      fun x y => ?_
    exact (hconv v ε hε i (w.1 v) ⟨w, rfl⟩ x y).const_mul _
  exact ⟨hpos, hIS, ⟨X, hWL X hWn, hXt⟩, ⟨Λ, fun b _ v => PBL.lamTop S b v, hLC1 Λ hLn, hLC2 _ hTn,
    fun b s hb hs hbs v => ⟨hΛ0 b s v, hΛs b s hb hs hbs v⟩, hTt⟩, hLC3 C₄ hPn hGo hSn⟩

def BuiltBounds2CptOfParts : Prop :=
  (P5.ThmPActualCpt → WaveLocB) → (P5.ThmPActualCpt → LiftLocB) → PBL.TopLocB →
  (P5.ThmPActualCpt → KB.DegTop) → (P5.ThmPActualCpt → Top.VecVTypes) → (P5.ThmPActualCpt → PBL.TopRatio) →
  (P5.ThmPActualCpt → GermLocB) → (P5.ThmPActualCpt → PosB) → (P5.ThmPActualCpt → IntB) →
  (P5.ThmPActualCpt → DecayUnif) → (P5.ThmPActualCpt → ThresholdsPositive) → KB.BuiltBounds2Cpt

theorem builtBounds2CptOfParts : BuiltBounds2CptOfParts := by
  intro hW hL hTL hDT hVT hTR hG hP hI hD hTh hA Cb
  exact core (hW hA) (hL hA) hTL (hDT hA) (hVT hA) (hTR hA) (hG hA) (hP hA) (hI hA) (hD hA) (hTh hA) Cb

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end
