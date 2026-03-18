#include <iostream>
#include <vector>
#include <exception>
#include <cmath>
#include <limits>
//Komentar Dino Tahirovic

const double PI=4*std::atan(1);
class ChebyshevApproximation{
double xmin;
double xmax;
std::vector<double> c;
int mdegree;
public:
ChebyshevApproximation(double xmin, double xmax, const std::vector<double>& c, int mdegree):xmin(xmin),xmax(xmax),c(c),mdegree(mdegree){}
template <typename FunType>
ChebyshevApproximation(FunType f, double xmin, double xmax, int n);
void set_m(int m){
    if(m<=1 || m>mdegree)throw std::domain_error("Bad order");
    mdegree=m;
}
void trunc(double eps){
    if(eps<0)throw std::domain_error("Bad tolerance");
    int n=mdegree;
    for(int i=0;i<=n;i++){
        bool flag=false;
        for(int j=i;j<=n;j++){
            if(std::fabs(c[j])>eps){
                flag=true;
                break;
            }
        }
        if(flag==false){
                if(i==0)throw std::domain_error("Bad tolerance");
            mdegree=i-1;
            c.resize(i);
            break;
        }
    }
}
void PrintC(){for(double x:c)std::cout<<x<<" ";std::cout<<std::endl;}
double operator()(double x) const{
    if(x>xmax || x<xmin)throw std::domain_error("Bad argument");
    double t=(2*x-xmin-xmax)/(xmax-xmin);
    double p=1;
    double q=t;
    double s=c[0]/2+c[1]*t;
    for(int k=2;k<=mdegree;k++){
        double r=2*t*q-p;
        s=s+c[k]*r;
        p=q;
        q=r;
    }
    return s;
}
double derivative(double x) const{
    if(x>xmax || x<xmin)throw std::domain_error("Bad argument");
    double t=(2*x-xmin-xmax)/(xmax-xmin);
    double p=1;
    double q=4*t;
    double s=c[1]+4*c[2]*t;
    for(int k=3;k<=mdegree;k++){
        double r=k*(2*t*q/(k-1)-p/(k-2));
        s=s+c[k]*r;
        p=q;
        q=r;
    }
    return 2*s/(xmax-xmin);
}
ChebyshevApproximation derivative() const{
    std::vector<double> cprim(mdegree);
    double mi=4/(xmax-xmin);
    cprim[mdegree-1]=mi*mdegree*c[mdegree];
    cprim[mdegree-2]=mi*(mdegree-1)*c[mdegree-1];
    for(int k=mdegree-3;k>=0;k--)cprim[k]=cprim[k+2]+mi*(k+1)*c[k+1];
    return ChebyshevApproximation(xmin,xmax,cprim,mdegree-1);
}
ChebyshevApproximation antiderivative() const{
    std::vector<double> canti(mdegree+2);
    double mi=(xmax-xmin)/4;
    canti[mdegree+1]=mi*c[mdegree]/(mdegree+1);
    canti[mdegree]=mi*c[mdegree-1]/mdegree;
    for(int k=1;k<mdegree;k++)canti[k]=mi*(c[k-1]-c[k+1])/k;
    return ChebyshevApproximation(xmin,xmax,canti,mdegree+1);
}
double integrate(double a, double b) const{
    if (a<xmin || a>xmax || b<xmin || b>xmax)throw std::domain_error("Bad interval");
    auto F(antiderivative());
    return F(b)-F(a);

}
double integrate() const{
    double sum=0;
    for(int k=1;k<=std::floor((mdegree+1)/2);k++)sum+=2*c[2*k]/(1-4*k*k);
    return (xmax-xmin)/2*sum+(xmax-xmin)/2*c[0];
}
};

template <typename FunType>
ChebyshevApproximation::ChebyshevApproximation(FunType f, double xmin, double xmax, int n):xmin(xmin), xmax(xmax), mdegree(n), c(n+1){
    if(xmin>=xmax || n<1)throw std::domain_error("Bad parameters");
    std::vector<double> w(4*n+4);
    std::vector<double> v(n+1);
    for(int i=0; i<4*n+4; i++)w[i]=std::cos(PI*i/(2*n+2));
    for(int i=0; i<=n; i++)v[i]=f((xmin+xmax+(xmax-xmin)*w[2*i+1])/2);
    for(int k=0; k<=n; k++){
        double s=0;
        for(int i=0; i<=n; i++)s=s+v[i]*w[(k*(2*i+1))%(4*n+4)];
        c[k]=2*s/(n+1);
    }
}




template <typename FunType>
 std::pair<double, bool> RombergIntegration(FunType f, double a, double b, double eps = 1e-8, int nmax = 1000000, int nmin = 50){
    if(eps<0 || nmin<0 || nmax<0 || nmax<nmin) throw std::domain_error("Bad parameter");
    int n=2;
    double h=(b-a)/n;
    double s=(f(a)+f(b))/2;
    double Iold=s;
    std::vector<double> I(nmax);
    for(int i=1;n<=nmax;i++){
        for(int j=1;j<=n/2;j++)s+=f(a+(2*j-1)*h);
        I[i-1]=h*s;
        double p=4;
        for(int k=i-1;k>=1;k--){
            I[k-1]=(p*I[k]-I[k-1])/(p-1);
            p*=4;
        }
        if(std::fabs(I[0]-Iold)<=eps)return {I[0],true};
         Iold=I[0];
         h/=2;
         n*=2;
    }

    return {Iold,false};
 }

 template <typename FunType>
 std::pair<double, bool> TanhSinhIntegration(FunType f, double a, double b, double eps = 1e-8, int nmax = 1000000, int nmin = 20, double range = 3.5){
    if(eps<0 || nmin<0 || nmax<0 || nmax<nmin || range<0) throw std::domain_error("Bad parameter");
    int n=2;
    double h=2*range/n;
    double p=(a+b)/2;
    double q=(b-a)/2;
    double s=0;
    double Iold=s;
    while(n<nmax){
        for(int i=1;i<=n/2;i++){
            double t=-range+(2*i-1)*h;
            double u=PI*std::sinh(t)/2;
            double v=f(p+q*std::tanh(u));
            if(std::isfinite(v))s+=q*PI*std::cosh(t)*v/(2*std::cosh(u)*std::cosh(u));
        }
        double I=h*s;
        if(n>=nmin && std::fabs(I-Iold)<=eps)return {I,true};
        Iold=I;
        n*=2;
        h/=2;
    }
    return {Iold,false};
 }


 template <typename FunType>
 double AdaptiveAux(FunType f, double a, double b, double eps, double f1, double f2, double f3, int r, bool& flag){
    if(!std::isfinite(f1))f1=0;
    if(!std::isfinite(f2))f2=0;
    if(!std::isfinite(f3))f3=0;

    double c=(a+b)/2;
    double i1=(b-a)*(f1+4*f3+f2)/6;
    double f4=f((a+c)/2);
    double f5=f((b+c)/2);
    double i2=(b-a)*(f1+4*f4+2*f3+4*f5+f2)/12;
    if(std::fabs(i1-i2)<=eps){
        return i2;
    }
    if(r<=0){flag=false;return i2;}
    return AdaptiveAux(f, a, c, eps, f1, f3, f4, r-1, flag)+AdaptiveAux(f, c, b, eps, f3, f2, f5, r-1, flag);
 }

 template <typename FunType>
 std::pair<double, bool> AdaptiveIntegration(FunType f, double a, double b, double eps = 1e-10, int maxdepth = 30, int nmin = 1){
    if(eps<0 || nmin<0 || maxdepth<0) throw std::domain_error("Bad parameter");
    bool flag=true;
    double s=0;
    double h=(b-a)/nmin;
    for(int i=1;i<=nmin;i++){
        s+=AdaptiveAux(f, a, a+h, eps, f(a), f(a+h), f(a+h/2), maxdepth, flag);
        a+=h;
    }
    return {s,flag};

 }



double f(double x){return std::exp(x);}
double f1(double x){return 1/x;}
double f2(double x){return 1/std::sqrt(x);}

int main(){/*
    double xmin=0;
    double xmax=1;
    int n=10;

    std::cout<<"konstrunktor, funktor\n";
    ChebyshevApproximation c(f, xmin, xmax, n);
    c.PrintC();
    c.trunc(0.0001);
    c.PrintC();
    std::cout<<c(0.5)<<std::endl;

    std::cout<<"izvodi\n";
    ChebyshevApproximation cprim=c.derivative();
    cprim.PrintC();
    std::cout<<c.derivative(0.5)<<std::endl;
    std::cout<<cprim(0.5)<<std::endl;

    ChebyshevApproximation cprim1=ChebyshevApproximation(xmin,xmax,{2, 0.5, -0.1, 0.05, 0.01},4).derivative();
    cprim1.PrintC();
    std::cout<<cprim1(0.5)<<std::endl;

    std::cout<<"integrali\n";
    ChebyshevApproximation canti=c.antiderivative();
    canti.PrintC();
    //std::cout<<c.derivative(0.5)<<std::endl;
    std::cout<<canti(0.5)<<std::endl;
    ChebyshevApproximation canti1=ChebyshevApproximation(xmin,xmax,{2, 0.5, -0.1, 0.05, 0.01},4).antiderivative();
    canti1.PrintC();
    std::cout<<canti1(0.5)<<std::endl;

    ChebyshevApproximation cintegrate(f1,1,2,8);
    cintegrate.PrintC();
    std::cout<<cintegrate.integrate(2,1)<<std::endl;
    std::cout<<cintegrate.integrate()<<std::endl;

    std::cout<<"Romberg\n";
    auto par=RombergIntegration(f1,1,2);
    std::cout<<par.first<<std::endl<<par.second<<std::endl;

    std::cout<<"tanhsinh\n";
    auto par1=TanhSinhIntegration(f2,0,1);
    std::cout<<par1.first<<std::endl<<par1.second<<std::endl;

    std::cout<<"Adaptive\n";
    auto par2=AdaptiveIntegration(f2,0,1);
    std::cout<<par2.first<<std::endl<<par2.second<<std::endl;*/

//AT18 - Adaptive integration - 9
auto aig =  AdaptiveIntegration([](double x) { return std::log(std::abs(x-1)); }, 0, 2, 1e-8, 15);
std::cout << aig.first << " " << aig.second;


    return 0;
}
