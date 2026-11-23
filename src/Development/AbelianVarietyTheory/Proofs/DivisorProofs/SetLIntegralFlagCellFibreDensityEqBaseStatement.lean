module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingCurry

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

noncomputable section
namespace GlobalTheory.FibDensMass

section Curry
variable {ι : Type} [Fintype ι] {κ : ι → Type} [∀ i, Fintype (κ i)] {Y : (i : ι) → κ i → Type}
  [∀ i j, MeasurableSpace (Y i j)]

theorem measurePreserving_curry (μ : ∀ i j, Measure (Y i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry Y) (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  apply _root_.GlobalTheory.ColFourier.measurePreserving_piCurry <;> assumption

end Curry

theorem lintegral_fin_prod {n : ℕ} {E : Fin n → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

theorem lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod fun i => hf _

theorem block_mass (s : ℕ) (A : Matrix (Fin s) (Fin s) ℂ) (hA : A.PosDef) :
    ∫⁻ w : Low s → ℂ, ENNReal.ofReal (GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens Aᵀ w) = 1 := by
  have hAt : Aᵀ.PosDef := hA.transpose
  have hd : 0 < A.det.re := (GlobalTheory.FlagFibre.FlagInt.re_facts hA).1
  have hc := GlobalTheory.TrueCx.flagConst_pos s
  have hk : 0 ≤ GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) := by positivity
  simp_rw [ENNReal.ofReal_mul hk]
  rw [lintegral_const_mul _ (GlobalTheory.FlagFibre.measurable_dens _).ennreal_ofReal,
    GlobalTheory.FlagFibre.FlagInt.lintegral_dens s Aᵀ hAt, Matrix.det_transpose, ← ENNReal.ofReal_mul hk]
  rw [← ENNReal.ofReal_one]
  congr 1
  have : A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ)) = 1 := by
    rw [← zpow_add₀ hd.ne']; simp
  calc GlobalTheory.TrueCx.flagConst s * A.det.re ^ ((s : ℤ) - 1) * (A.det.re ^ (1 - (s : ℤ)) / GlobalTheory.TrueCx.flagConst s)
        = (A.det.re ^ ((s : ℤ) - 1) * A.det.re ^ (1 - (s : ℤ))) * (GlobalTheory.TrueCx.flagConst s / GlobalTheory.TrueCx.flagConst s) := by ring
    _ = 1 := by rw [this, div_self hc.ne', one_mul]

end GlobalTheory.FibDensMass

open GlobalTheory.FibDensMass in
theorem GlobalTheory.FlagCell2.fibDens_mass : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (G : Mat m ℂ), (∀ τ, (G τ).PosDef) → (∀ y, 0 ≤ fibDens G y) ∧ ∫⁻ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = 1 := by
  intro ι _ m G hG
  have hnn : ∀ τ (w : Low (m τ) → ℂ), 0 ≤ GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) *
      GlobalTheory.FlagFibre.dens (G τ)ᵀ w := fun τ w =>
    mul_nonneg (mul_nonneg (GlobalTheory.TrueCx.flagConst_pos _).le
      (zpow_nonneg (GlobalTheory.FlagFibre.FlagInt.re_facts (hG τ)).1.le _)) (GlobalTheory.FlagFibre.dens_nonneg _ _)
  refine ⟨fun y => Finset.prod_nonneg fun τ _ => hnn τ _, ?_⟩
  have hmp := measurePreserving_curry (Y := fun (τ : ι) (_ : Low (m τ)) => ℂ) (fun _ _ => (volume : Measure ℂ))
  let g : ∀ τ, (Low (m τ) → ℂ) → ℝ≥0∞ := fun τ w => ENNReal.ofReal (GlobalTheory.TrueCx.flagConst (m τ) *
    (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ w)
  have hpt : ∀ y : Cell m → ℂ, ENNReal.ofReal (fibDens G y) = ∏ τ, g τ (MeasurableEquiv.piCurry (fun (τ : ι) (_ : Low (m τ)) => ℂ) y τ) := by
    intro y
    simp only [fibDens, g]
    rw [ENNReal.ofReal_prod_of_nonneg fun τ _ => hnn τ _]
    rfl
  simp_rw [hpt]
  rw [show (volume : Measure (Cell m → ℂ)) = Measure.pi fun p : Cell m => (volume : Measure ℂ) from rfl,
    hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) (fun z => ∏ τ, g τ (z τ))]
  rw [lintegral_fintype_prod (μ := fun τ => Measure.pi fun _ : Low (m τ) => (volume : Measure ℂ))
    fun τ => ((GlobalTheory.FlagFibre.measurable_dens _).const_mul _).ennreal_ofReal.aemeasurable]
  exact Finset.prod_eq_one fun τ _ => block_mass (m τ) (G τ) (hG τ)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPtSplit

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

noncomputable def ptEquiv (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) : V d × (J → ℂ) ≃ᵐ V n :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm (MeasurableEquiv.refl (J → ℂ))).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm).trans
    ((MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)).trans (MeasurableEquiv.toLp 2 (Fin n → ℂ)))

theorem ptEquiv_apply (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (x : V d × (J → ℂ)) :
    ptEquiv n d J ε x = pt ε x.1 x.2 := by
  ext i
  change (Equiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm (x.1.ofLp, x.2) (ε i) = Sum.elim (fun a => x.1.ofLp a) x.2 (ε i)
  cases ε i <;> rfl

theorem measurePreserving_pt_split : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J),
    MeasurePreserving (fun x : V d × (J → ℂ) => pt ε x.1 x.2) volume volume ∧
      MeasurableEmbedding (fun x : V d × (J → ℂ) => pt ε x.1 x.2) := by
  intro n d J _ ε
  have e : (fun x : V d × (J → ℂ) => pt ε x.1 x.2) = ⇑(ptEquiv n d J ε) := by
    funext x; exact (ptEquiv_apply n d J ε x).symm
  rw [e]
  refine ⟨?_, (ptEquiv n d J ε).measurableEmbedding⟩
  have h1 : MeasurePreserving (fun z : V d => z.ofLp) volume volume := volume_preserving_ofLp_complex (Fin d)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure (J → ℂ)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ J => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm (volume_preserving_ofLp_complex (Fin n))
  exact h5.comp h4

end GlobalTheory.FlagCell2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBase

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem aemeasurable_fibDens {ι : Type} [Fintype ι] {m : ι → ℕ} {d : ℕ} (G : V d → Mat m ℂ) (O : Set (V d))
    (hO : IsOpen O) (hG : ∀ τ i j, ContinuousOn (fun v => G v τ i j) O) :
    AEMeasurable (fun x : V d × (Cell m → ℂ) => fibDens (G x.1) x.2)
      (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hGτ : ∀ τ, ContinuousOn (fun x : V d × (Cell m → ℂ) => G x.1 τ) (O ×ˢ Set.univ) := by
    intro τ
    have h : ContinuousOn (fun v => G v τ) O :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hG τ i j
    exact h.comp continuous_fst.continuousOn fun x hx => hx.1
  unfold fibDens
  apply Finset.aemeasurable_fun_prod
  intro τ _
  refine AEMeasurable.mul (AEMeasurable.mul aemeasurable_const ?_) ?_
  · have h := ((continuous_id.matrix_det).comp_continuousOn (hGτ τ))
    exact ((Complex.continuous_re.comp_continuousOn h).aemeasurable hS).pow_const _
  · unfold GlobalTheory.FlagFibre.dens
    apply Finset.aemeasurable_fun_prod
    intro i _
    refine AEMeasurable.pow_const (AEMeasurable.norm ?_) _
    have hc : Continuous fun p : Matrix (Fin (m τ)) (Fin (m τ)) ℂ × (Low (m τ) → ℂ) =>
        ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni p.2)ᴴ * p.1ᵀ * GlobalTheory.FlagFibre.uni p.2) i.castSucc := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      exact ((((GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd).matrix_conjTranspose.matrix_mul
        continuous_fst.matrix_transpose).matrix_mul (GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd)).matrix_submatrix
        _ _).matrix_det
    have h2 : ContinuousOn (fun x : V d × (Cell m → ℂ) => (G x.1 τ, fun s => x.2 ⟨τ, s⟩)) (O ×ˢ Set.univ) :=
      (hGτ τ).prodMk (by fun_prop : Continuous fun x : V d × (Cell m → ℂ) => fun s => x.2 ⟨τ, s⟩).continuousOn
    exact (hc.comp_continuousOn h2).aemeasurable hS

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem setLIntegral_fibDens : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  intro ι _ m n d ε G δ O K hO hK hKO hδ hG hpos
  have hmp := (GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).1
  have hb : Measurable (bsL ε) := (bsL ε).continuous.measurable
  have hm := hmp.restrict_preimage (hb hK)
  have hs : (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ⁻¹' (bsL ε ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [bsL_pt]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  set F : V d × (Cell m → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (δ x.1 * fibDens (G x.1) x.2) with hF
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hFO : AEMeasurable F (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable (AEMeasurable.mul ?_ (aemeasurable_fibDens G O hO hG))
    exact (hδ.comp continuous_fst.continuousOn (fun x (hx : x ∈ O ×ˢ (Set.univ : Set (Cell m → ℂ))) => hx.1)).aemeasurable hS
  have hFK : AEMeasurable F ((volume.restrict K).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Cell m → ℂ))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    exact hFO.mono_measure (Measure.restrict_mono (Set.prod_mono hKO subset_rfl) le_rfl)
  have e1 : (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w))) ∘
      (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) = F := by
    funext x
    simp [hF, bsL_pt, fb_pt]
  have hH : AEMeasurable (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)))
      (Measure.map (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ((volume.restrict K).prod volume)) := by
    rw [(GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).2.aemeasurable_map_iff, e1]
    exact hFK
  rw [← hm.map_eq, lintegral_map' hH hm.measurable.aemeasurable]
  refine (lintegral_congr fun a => congrFun e1 a).trans ?_
  rw [lintegral_prod _ hFK]
  refine setLIntegral_congr_fun hK fun v hv => ?_
  obtain ⟨h0, h1⟩ := GlobalTheory.FlagCell2.fibDens_mass ι m (G v) (hpos v (hKO hv))
  simp only [hF]
  simp_rw [ENNReal.ofReal_mul' (h0 _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, mul_one]

end GlobalTheory.FlagCell2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBaseStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.setLIntegral_flagCellFibreDensity_eq_base : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  first | exact @GlobalTheory.FlagCell2.setLIntegral_fibDens | exact GlobalTheory.FlagCell2.setLIntegral_fibDens | (intros; apply GlobalTheory.FlagCell2.setLIntegral_fibDens <;> assumption)
end
end
