module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstOrbitParabolicLeft
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InjCoreK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.LagrangianConditionParabolicMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StabDecK
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeylBaseColumn

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
namespace N
theorem fix_of_col_k {w x : d.G}
    (hc : ∀ r, inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w⁻¹ * x) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
theorem weyl_base_column (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (F := F) (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.weyl_base_column h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2 (by rw [hpm, Matrix.toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = Matrix.fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2 (by rw [hpn, Matrix.toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := Matrix.fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.fix_of_col_k fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hpn, hpm, hG0, kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]
end N
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.NormalizeK

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem normalize_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (w₁⁻¹ * (p * γ)) :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.C6.N.normalize_k h hγ hn
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitBijectionWeyl

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4
namespace PositivityTheory.SiegelWeilFormula.Act.C6
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem second_orbit_bijection_weyl (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1))) := by
  have hg : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L), w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)) ∈ rat2 σ d.Y := fun x =>
    (rat2 σ d.Y).mul_mem h.wr ((rat2 σ d.Y).mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.cM_rat'_k h x.2.2.1 x.2.2.2) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.j_rat_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd x.1)))
  have hfix : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Fix_k L (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)) := fun x => _root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_mul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_cM'_k h _) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.fix_j_k _)
  let Fm : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.Cr_k L) → {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} := fun x =>
    ⟨Quotient.mk _ ⟨_, hg x⟩, by
      obtain ⟨p, hp, -, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k d ⟨_, hg x⟩
      rw [e, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.first_orbit_parabolic_left hp]
      exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.not_first_orbit_weyl h (hfix x)⟩
  have hinj : Function.Injective Fm := by
    rintro ⟨q₁, c₁⟩ ⟨q₂, c₂⟩ hE
    have hE' : (Quotient.mk _ ⟨_, hg ⟨q₁, c₁⟩⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = Quotient.mk _ ⟨_, hg ⟨q₂, c₂⟩⟩ := congrArg Subtype.val hE
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k] at hE'
    set g₁ := w₁ * (cM c₁.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₁))
    set g₂ := w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₂))
    have e : (g₂ * g₁⁻¹) * (w₁ * (cM c₁.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₁))) = w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q₂)) := by
      simp only [g₁, g₂]; group
    have hpr : g₂ * g₁⁻¹ ∈ rat2 σ d.Y := (rat2 σ d.Y).mul_mem (hg ⟨q₂, c₂⟩) ((rat2 σ d.Y).inv_mem (hg ⟨q₁, c₁⟩))
    obtain ⟨hP, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.inj_core_k h hE' hpr (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd q₁) (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k L.sd q₂) e
    have hq : q₁ = q₂ := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k L.sd q₁, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k L.sd q₂, _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k]
      exact hP
    subst hq
    rw [hc rfl]
  have hsurj : Function.Surjective Fm := by
    rintro ⟨q, hq⟩
    obtain ⟨p, hp, hpr, hfx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.normalize_k h (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q) hq
    have hr : w₁⁻¹ * (p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) ∈ rat2 σ d.Y :=
      (rat2 σ d.Y).mul_mem ((rat2 σ d.Y).inv_mem h.wr) ((rat2 σ d.Y).mul_mem hpr (_root_.PositivityTheory.SiegelWeilFormula.Act.C6.rep_mem_k d q))
    obtain ⟨s, c, γ', hsr, hW, hγ', -, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.stab_dec_k h hr hfx
    obtain ⟨p', hp', hp'r, he'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k L.sd ⟨γ', hγ'⟩
    obtain ⟨p₂, hp₂, hp₂r, c₂, hc₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.conj_par_k h ((par2 σ L.Y).inv_mem hp') ((rat2 σ L.Y).inv_mem hp'r) c
    refine ⟨⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩, Subtype.ext ?_⟩
    show (Quotient.mk _ ⟨_, hg ⟨Quotient.mk _ ⟨γ', hγ'⟩, c₂⟩⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) = q
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_rep_k d q]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C6.mk_eq_mk_k]
    have hγ'' : γ' = p'⁻¹ * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd) := by rw [he']; group
    have key : p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q = (w₁ * s * w₁⁻¹) * p₂ * (w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd)))) := by
      have h1 : p * _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q = w₁ * (s * (cM c.1 * L.j γ')) := by rw [← hx]; group
      rw [h1]
      conv_lhs => rw [hγ'', map_mul]
      have h2 : w₁ * (s * (cM c.1 * (L.j p'⁻¹ * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))))) =
          (w₁ * s * w₁⁻¹) * ((w₁ * (cM c.1 * L.j p'⁻¹)) * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))) := by group
      rw [h2, hc₂]
      group
    have : _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q * (w₁ * (cM c₂.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (Quotient.mk _ ⟨γ', hγ'⟩ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd))))⁻¹ = p⁻¹ * ((w₁ * s * w₁⁻¹) * p₂) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, key]; group
    rw [this]
    exact (par2 σ d.Y).mul_mem ((par2 σ d.Y).inv_mem hp) ((par2 σ d.Y).mul_mem hW hp₂)
  refine ⟨Equiv.ofBijective Fm ⟨hinj, hsurj⟩, fun x => ?_⟩
  obtain ⟨p, hp, hpr, e⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C6.out_mk_k d ⟨_, hg x⟩
  exact ⟨p, hp, hpr, e⟩
end PositivityTheory.SiegelWeilFormula.Act.C6
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitBijection

section

@[expose] public section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
abbrev Crat_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Type := {c : (Fin L.n → AE F E) × AF F // c.1 ∈ L.ratV ∧ c.2 ∈ (algebraMap F (AF F)).range}
theorem second_orbit_bijection (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) :
    ∃ e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧
      _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1))) := by
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C6.second_orbit_bijection_weyl ⟨h.nb, h.uM, h.nb', h.wr, h.wf, h.cf, h.δ0⟩
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end
end
