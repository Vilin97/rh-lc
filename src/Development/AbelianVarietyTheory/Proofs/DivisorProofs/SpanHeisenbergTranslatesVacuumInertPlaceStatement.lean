module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerIrreducibleFinitePlaceCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocZero

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertAvg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tens_inj (v : Pl (F := F)) {κ : Type} (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRt : ∀ x z, At (evFin F v) z → R (x + z) = R x) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (e : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hRt 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

section Grp
variable {n : ℕ} {W : Spc F E n}

end Grp

section Loc
variable {a a' : ℕ} {B : Base F E} (G : Geo σ a a') {X : Chars F E}


variable {G} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

end Loc

end GlobalTheory.InertAvg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerTranslatesSpanSchwartz

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchrSpan

theorem schr_comp_loc {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  have h2 : (2 : R) * ⅟(2 : R) = 1 := mul_invOf_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2

theorem mem_span_schr_of_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) [Invertible (2 : Fv F v)] (χ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ], (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, χ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    ∀ (f₀ : (κ → Fv F v) → ℂ), f₀ ∈ SB (κ → Fv F v) → f₀ ≠ 0 → ∀ (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) →
      φ ∈ Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr χ w f₀) := by
  intro F _ _ v _ χ κ _ hcond f₀ hf₀ hne φ hφ
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have htriv : ∀ y ∈ v.adicCompletionIntegers F, χ y = 1 := by
    intro y hy
    have := (hcond 1).2 (one_mem _) y hy
    simpa using this
  have hc : Continuous χ := by
    have : IsLocallyConstant χ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      rw [← map_add_left_nhds_zero, Filter.eventually_map]
      filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
      rw [AddChar.map_add_eq_mul, htriv s hs, mul_one]
    exact this.continuous
  have h1 : χ ≠ 1 := by
    intro h
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hπ0 : π ≠ 0 := by
      intro h0; rw [h0, map_zero] at hπ; exact WithZero.zero_ne_coe hπ
    have hmem : ((π⁻¹ : F) : Fv F v) ∈ v.adicCompletionIntegers F :=
      (hcond _).1 (fun y _ => by rw [h]; rfl)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, hπ] at hmem
    exact absurd hmem (by decide)
  set N := Submodule.span ℂ (Set.range fun w : (κ → Fv F v) × (κ → Fv F v) => schr χ w f₀) with hNdef
  have hN : N ≤ GlobalTheory.WeilM.SB (κ → Fv F v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    show schr χ w f₀ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)
    convert GlobalTheory.SchrSBFin.schr_mem_SB v χ hc w f₀ hf₀ using 2
    all_goals exact Subsingleton.elim _ _
  have hS : ∀ w, ∀ g ∈ N, schr χ w g ∈ N := by
    intro w g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w', rfl⟩ := hx
      rw [schr_comp_loc]
      exact N.smul_mem _ (Submodule.subset_span ⟨w + w', rfl⟩)
    | zero =>
      have : schr χ w (0 : (κ → Fv F v) → ℂ) = 0 := by funext x; simp [schr]
      rw [this]; exact N.zero_mem
    | add a b _ _ ha hb =>
      have : schr χ w (a + b) = schr χ w a + schr χ w b := by funext x; simp [schr, mul_add]
      rw [this]; exact N.add_mem ha hb
    | smul c a _ ha =>
      have : schr χ w (c • a) = c • schr χ w a := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
      rw [this]; exact N.smul_mem c ha
  have h0 : f₀ ∈ N := by
    have : schr χ (0 : (κ → Fv F v) × (κ → Fv F v)) f₀ = f₀ := by funext x; simp [schr]
    rw [← this]; exact Submodule.subset_span ⟨0, rfl⟩
  have hall := GlobalTheory.SchrIrred.schr_irreducible v χ hc h1 N hN
    (fun w g hg => by convert hS w g hg using 2; exact Subsingleton.elim _ _) f₀ h0 hne
  rw [hall]; exact hφ

end GlobalTheory.SchrSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesVacuumInertPlace

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

open scoped GlobalTheory.VacAny

namespace GlobalTheory.InertSpan

theorem span_translates_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ s hs
  obtain ⟨-, -, -, -, -, -, -, -, -, hAt, hSurj, -⟩ := hC
  have hunr : PsiUnr B.ψ v := (hT.base.inert v w hw).2.2
  have hvac := hT.geo.hM'.vac v
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
  have key : ∀ x, ((ρ x s : SB _) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) =
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (κ x)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    fun x => GlobalTheory.InertAvg.tens_inj v R hR0 (hR _ s.2).1
      ((hρ x s R (hR _ s.2)).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo _ _ v _ (hAt x) _ R (hR _ s.2)))
  have hsurj : ∀ p : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v),
      ∃ x, GlobalTheory.LatVac.locCo G.M'.co v (κ x) = p := by
    intro p
    obtain ⟨x, hx⟩ := hSurj (G.M'.co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)))
      (by
        intro u hu
        rw [← LinearEquiv.map_smul]
        convert G.M'.co.e.symm.map_zero using 2
        ext k
        · exact GlobalTheory.LatVac.at_liftV v (p.1 k) u hu
        · exact GlobalTheory.LatVac.at_liftV v (p.2 k) u hu)
    refine ⟨x, ?_⟩
    rw [hx]
    ext k
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
    · simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]
  have hs0 : (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ≠ 0 := hs ▸ hvac.2.1
  have hcond : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ v.adicCompletionIntegers F := hunr
  have hrange : Set.range (fun p => schr (GlobalTheory.LatVac.psiAt B.ψ v) p (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) =
      (SB (Fin a' × Fin (a + a') → Fv F v)).subtype '' Set.range (fun x => ρ x s) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx⟩ := hsurj p
      exact ⟨ρ x s, ⟨x, rfl⟩, by rw [Submodule.subtype_apply, key, hx]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, (key x).symm⟩
  rw [eq_top_iff]
  rintro m -
  have hm := GlobalTheory.SchrSpan.mem_span_schr_of_mem_SB F v (GlobalTheory.LatVac.psiAt B.ψ v) _ hcond _ s.2 hs0 _ m.2
  rw [hrange, Submodule.span_image] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  rwa [← Subtype.ext hnm]

end GlobalTheory.InertSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanHeisenbergTranslatesVacuumInertPlaceStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.span_heisenbergTranslates_vacuum_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
      Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ := by
  first | exact @GlobalTheory.InertSpan.span_translates_vac | exact GlobalTheory.InertSpan.span_translates_vac | (intros; apply GlobalTheory.InertSpan.span_translates_vac <;> assumption)
end
end
