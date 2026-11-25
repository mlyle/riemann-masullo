"""Certify a simple critical zero of beta and its one-mode prime excursion amplitude."""
from argparse import ArgumentParser
from flint import acb, acb_series, arb, ctx, dirichlet_char


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 96
    ctx.prec = args.precision
    chi = dirichlet_char(4, 3)
    lo = arb("6.02094890469")
    hi = arb("6.02094890471")
    assert chi.hardy_z(lo).real > 0 and chi.hardy_z(hi).real < 0
    gamma = lo.union(hi)
    point = acb(arb(1)/2, gamma)
    derivative = acb_series([point, 1], prec=2).dirichlet_l(chi)[1]
    assert abs(derivative) > 1
    def arch(z):
        return (acb(4)/acb.pi())**((z+1)/2) * ((z+1)/2).gamma()
    center = acb(arb(1)/2)
    center_value = (arch(center)*center.dirichlet_l(chi)).real
    amplitude = gamma*abs(arch(point)*derivative)/(center_value*abs(point*(point+1)))
    assert amplitude > arb("0.00749220") and amplitude < arb("0.00749222")
    assert arb(2)/3-amplitude < arb("0.65918")
    assert arb(2)/3+amplitude > arb("0.67415")
    print("precision",ctx.prec)
    print("zero height",gamma)
    print("magnitude of beta derivative",abs(derivative))
    print("completed beta at 1/2",center_value)
    print("positive single-mode amplitude",amplitude)
    print("lower and upper deficits at the extrema", arb(2)/3-amplitude, arb(2)/3+amplitude)


if __name__=="__main__":
    main()
