import MonoidProduct.Certificates.Basic
set_option linter.style.header false

/-!
# Outputs determined by other outputs

If `g S` depends only on `f S` (`∀ S T, f S = f T → g S = g T`), every strong certificate for
`f` is one for `g`, so `b_g ≤ b_f` (`strongCertificateSize_le_of_determined`).  This is
`strongCertificateSize_postcomp_le` without naming the readout `O → O'`: it applies when `g` is
only known to be a function of `f`, as for readouts of failure profiles.
-/

namespace MonoidProduct.Certificates

variable {U O O' : Type*} [DecidableEq U] {f : Finset U → O} {g : Finset U → O'}

/-- A strong certificate for `f` is one for every output determined by `f`. -/
theorem IsStrongCertificate.of_determined (h : ∀ S T, f S = f T → g S = g T)
    {C S : Finset U} (hC : IsStrongCertificate f C S) : IsStrongCertificate g C S :=
  ⟨hC.1, fun K => h _ _ (hC.2 K)⟩

/-- A certificate bound for `f` is one for every output determined by `f`. -/
theorem HasStrongCertificateBound.of_determined (h : ∀ S T, f S = f T → g S = g T) {b : ℕ}
    (hf : HasStrongCertificateBound f b) : HasStrongCertificateBound g b := fun S => by
  obtain ⟨C, hC, hcard⟩ := hf S
  exact ⟨C, hC.of_determined h, hcard⟩

/-- **Outputs determined by `f` have certificate size at most `b_f`.** -/
theorem strongCertificateSize_le_of_determined [Finite U] (h : ∀ S T, f S = f T → g S = g T) :
    strongCertificateSize g ≤ strongCertificateSize f :=
  strongCertificateSize_le ((hasStrongCertificateBound_strongCertificateSize f).of_determined h)

end MonoidProduct.Certificates
