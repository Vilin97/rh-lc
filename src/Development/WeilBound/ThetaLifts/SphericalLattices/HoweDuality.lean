module

public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoMemOfMkEq
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSchroedingerFamilyAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeVacuumFixedAndUniqueStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
public import Development.WeilBound.ThetaLifts.SphericalLattices.LocDataVAlt
public import Development.WeilBound.ThetaLifts.SphericalLattices.UnrAtDiv

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.GenOf

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem gen_of {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
    {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}
    (hL : IsLocRep M ψ om v ω ρ) (hD : LocData M om v) :
    (∀ φ ∈ SB _, (∀ g ∈ KAt σ X v, ω (g, 1) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)}) ∧
    (∀ φ ∈ SB _, (∀ k ∈ KAt σ W v, ω (1, k) φ = φ) →
      φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), z = ω (g, 1) (M.vac v)}) := by
  obtain ⟨L, _, _, _, _, ϖ, σL, q, δ, JS, JT, ψL, ρL, ωL, ιS, ιT, s, hP, hs0, hsv, hspan, hsvac,
    hιS, hιT, hKS, hKT, hLoc⟩ := hD
  obtain ⟨h1, h2⟩ := GlobalTheory.Hk3.howeUnram_holds _ _ _ _ _ _ _ _ _ _ _ _ _ hP s hs0 hsv hspan
  have key : ∀ g h m, (↑(ωL (g, h) m) : Fn F n d v) = ω (ιS g, ιT h) ↑m := by
    intro g h m
    have hφ₁ := hL.pres _ (hιS g) _ (hιT h) _ m.2
    exact (hLoc g h m _ hφ₁).1 ((hL.acts _ (hιS g) _ (hιT h) _ m.2 _).2 rfl)
  have hS1 : ιS 1 = 1 := map_one ιS
  have hT1 : ιT 1 = 1 := map_one ιT
  constructor
  · intro φ hφ hfix
    have hw := h1 ⟨φ, hφ⟩ fun g hg => by
      apply Subtype.ext
      rw [key, hT1]
      exact hfix _ (by rw [kAt_eq]; exact hKS g hg)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιT h, hιT h, by rw [Submodule.subtype_apply, key, hS1, hsvac]⟩
  · intro φ hφ hfix
    have hw := h2 ⟨φ, hφ⟩ fun h hh => by
      apply Subtype.ext
      rw [key, hS1]
      exact hfix _ (by rw [kAt_eq]; exact hKT h hh)
    have hmap := Submodule.mem_map_of_mem (f := Submodule.subtype _) hw
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq]
    exact ⟨ιS g, hιS g, by rw [Submodule.subtype_apply, key, hT1, hsvac]⟩

end PositivityTheory.Sph

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExistsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inert_place_local_field_data_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : Valued L (WithZero (Multiplicative ℤ))) (_ : CompleteSpace L)
      (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧ (Valued.v δ = 1 ∧ σL δ = -δ) ∧
      (∀ x ∈ Formalism.UG.intL L, σL x = x → ψL x = 1) ∧ (∃ x ∈ Formalism.UG.intL L, σL x = x ∧ ψL (ϖ⁻¹ * x) ≠ 1) ∧
      Function.Injective ι ∧ (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) ∧
      (∀ x y, ι (x * y) = ι x * ι y) ∧ (∀ x, ι (σL x) = cA σ (ι x)) ∧
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) ∧
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) := by
  first | exact @GlobalTheory.InertLocField.field_data | exact GlobalTheory.InertLocField.field_data | (intros; apply GlobalTheory.InertLocField.field_data <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinatesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  first | exact @GlobalTheory.InertLocFrame.frame | exact GlobalTheory.InertLocFrame.frame | (intros; apply GlobalTheory.InertLocFrame.frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperator

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocModel

theorem weil_normalises_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v
  have hS := IsUWeilPair.isUSplitting hT.weil
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1
  simp only [Module.End.mul_apply]
  have h1 := (hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)
  have h2 := hρ x φ R (hR _ φ.2)
  have h3 := (hω g φ _).2 rfl R (hR _ φ.2)
  have h4 := hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)
  have h5 := hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2
  rw [← h1, ← h4, ← h2, h5, hact, h3]

end GlobalTheory.InertLocModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperatorStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  first | exact @GlobalTheory.InertLocModel.weil_normalises_schr | exact GlobalTheory.InertLocModel.weil_normalises_schr | (intros; apply GlobalTheory.InertLocModel.weil_normalises_schr <;> assumption)
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.LocDataV

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem locDataV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hin : Formalism.UG.IsInertAt F E v w)
    (hvT : v ∉ X.T) : LocData G.M om v := by
  obtain ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, ψL, ι, hunr, hodd, hδ, hpi, hpn, hinj, him, hmul, hσ, hint, hψ⟩ :=
    GlobalTheory.T.inert_place_local_field_data_exists F E σ B hT.base v w hin
  obtain ⟨JS, JT, Xm, iV, iW, hiS, hiT, hhS, hhT, hψ2, himX, hlat1, hlat2, hact, hUV, hUW, hKV, hKW⟩ :=
    GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates F E σ B a a' G hT.base hT.geo v w hin L ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ
  obtain ⟨ρ, hρ0, hρmul, hρA, hρspan⟩ := GlobalTheory.T.exists_local_schroedinger_family_at_place F v B.ψ hT.base.std (hT.base.inert v w hin).2.2 G.M.co
    (Matrix (Fin (a + a')) (Fin a) L) Xm
    (fun x y => ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) himX hψ2
  let j := iV.prodMap iW
  obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_localWeilOperators_supportedAtPlace F E σ B a a' G X om om' hT v _ j (fun g => ⟨hUV g.1, hUW g.2⟩)
  have hnorm := GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator F E σ B a a' G X om om' hT v _ Xm (fun y => (himX _).2 ⟨y, rfl⟩) ρ hρA _ j ω hω
    (fun g x => ((g.2 : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g.1 : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) (fun g x => hact g.1 g.2 x)
  obtain ⟨hvac, huniq⟩ := GlobalTheory.T.inertPlace_latticeVacuum_fixed_and_unique F E σ B a a' G X om om' hT v w hin hvT _ Xm
    (fun u => ∀ i j, u i j ∈ Formalism.UG.intL L) hlat1 hlat2 ρ hρA
  have hfix := GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hin hvT
  have hvSB := (hT.geo.hM.vac v).1
  have hv0 := (hT.geo.hM.vac v).2.1
  let s : SB (Fin a × Fin (a + a') → Fv F v) := ⟨G.M.vac v, hvSB⟩
  have hs0 : s ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hspan := hρspan s hs0
  have hωs : ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
    intro g h hg hh
    exact Subtype.ext ((hω (g, h) s (G.M.vac v)).1 (hfix _ (hKV g hg) _ (hKW h hh))).symm
  refine ⟨L, iF, iC, iVl, iCS, ϖ, σL, q, δ, JS, JT, ψL, ρ, ω, iV, iW, s, ?_, hs0, fun u hu => hvac s rfl u hu, hspan, rfl,
    hUV, hUW, hKV, hKW, fun g h m φ₁ _ => (hω (g, h) m φ₁).trans eq_comm⟩
  exact
    { unr := hunr
      odd := hodd
      intS := hiS
      intT := hiT
      hermS := hhS
      hermT := hhT
      delta := hδ
      psi_int := hpi
      psi_ne := hpn
      rho_zero := hρ0
      rho_mul := hρmul
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, s, fun u hu => hvac s rfl u hu, rfl⟩
      norm := fun g h x => hnorm (g, h) x
      fix := by
        intro g h hg hh s' hs'
        obtain ⟨c, hc⟩ := huniq s' hs'
        have e : s' = c • s := Subtype.ext hc
        rw [e, map_smul, hωs g h hg hh] }

end PositivityTheory.Sph

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.HoweDuality

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem howeInert : HoweInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he
  obtain ⟨⟨w, hin⟩, hvT⟩ := inert_ctx hT he
  have ha : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.α u :=
    fun u hu => hT.chars.unrα u fun h => hvT (hu ▸ h)
  have hb : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v → UnrAt X.β u :=
    fun u hu => hT.chars.unrβ u fun h => hvT (hu ▸ h)
  refine ⟨fun ω ρ hL => ?_, fun ω ρ hL => ?_⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hb
      (fun u hu => unrAt_div (hb u hu) (ha u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2⟩ := fix_of hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' ha
      (fun u hu => unrAt_div (ha u hu) (hb u hu)) hL
    obtain ⟨h3, h4⟩ := gen_of hL (locDataV' hT hin hvT)
    exact ⟨h1, h2, h3, h4⟩

end PositivityTheory.Sph

end
end
end
