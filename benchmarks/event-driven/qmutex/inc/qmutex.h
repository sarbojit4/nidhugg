#ifdef _USE_PTHREADS
#  include "qmutex_pthread.h"
#else
#  include "qmutex_qthread.h"
#endif
