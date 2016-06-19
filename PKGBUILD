# Maintainer: Moritz Lipp <mlq@pwmt.org>

pkgname=bear
pkgver=2.1.5
pkgrel=1
pkgdesc="tool to generate compilation database for clang tooling"
arch=('i686' 'x86_64')
url="https://github.com/rizsotto/Bear"
license=('GPL3')
makedepends=('cmake' 'make')
depends=('python>=2.7')
conflicts=('bear')
provides=('bear')
source=(bear.tar.xz)
md5sums=('SKIP')

build() {
  cd "$srcdir"/bear
  cmake \
    -DCMAKE_INSTALL_PREFIX=/usr \
    -DCMAKE_INSTALL_SYSCONFDIR=/etc \
    .
  make all
}

package() {
  cd "$srcdir"/bear
  make DESTDIR="$pkgdir/" install

  if [ $CARCH = "x86_64" ]; then
    mv $pkgdir/usr/lib64 $pkgdir/usr/lib
  fi
}
