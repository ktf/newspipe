#!/usr/bin/env python
# -*- coding: UTF-8 -*-

# $NoKeywords: $   for Visual Sourcesafe, stop replacing tags
__revision__ = "$Revision: 1.7 $"
__revision_number__ = __revision__.split()[1]
__url__ = "https://newspipe.sourceforge.net"
__author__ = "Ricardo M. Reyes <reyesric@ufasta.edu.ar>"
__id__ = "$Id: cache.py,v 1.7 2004/11/21 23:00:48 reyesric Exp $"

from glob import glob
from pickle import load, dump
import md5
from pprint import pprint
from datetime import datetime, timedelta
import os
import os.path
from urlparse import urlparse, urlunparse
from urllib2 import urlopen, Request, HTTPError
import email.Utils
import gzip
import StringIO
import stat
import Queue
import time
from os import popen
from urllib2 import URLError
import base64

try:
    import threading as _threading
except ImportError:
    import dummy_threading as _threading

    
import socket
socket.setdefaulttimeout (60)

try:
    from feedparser import parse
    _has_feedparser = True
except ImportError:
    _has_feedparser = False

def touchFile (x):
    os.utime (x, None)
# end def    

def normalizeUrl (url):
    """ Remove double / before the selector part of a url

        schema://domain/SELECTOR

    It seems that urllib2.urlopen chokes on urls of the form

        schema://domain//selector

    """
        

    p = list(urlparse(url))
    if p[2].startswith('//'):
        aux = p[2][1:]
        p[2] = aux
    # end if
    return urlunparse(p)
# end def


class FileInfo:
    def __init__(self, content, info, url):
        self.url = url
        self.info = info
        self.content = content
# end class

class OfflineError (Exception):
    def __init__(self):
        Exception.__init__(self)

    def __str__(self):
        return 'Resource unavailable (offline)'
    # end def    
# end class

class Cache:
    def __init__(self, location, agent=None, offline=False, debug=False):
        self.offline = offline
        self.debug = debug
        self.location = os.path.abspath(location)

        try:
            os.makedirs(self.location)
        except OSError, e:
            if e.errno == 17:  # errno 17 means the directory already exists
                pass
            else:
                raise
            # end if
        # end try

        if agent:
            self.agent = agent
        else:
            self.agent = 'cache lib (rev. '+__revision_number__+')'
        # end if

    def checksum(self, texto):
        m = md5.new()
        m.update (texto)
        return m.hexdigest()
    # end def    
        
    def urlopen(self, url, max_age=None, referer=None, can_pipe=False, username=None, password=None):
        if can_pipe:
            if url.lower().startswith('pipe://'):
                path = url[7:]
                process = popen (path, 'r')
                data = process.read()

                new_info = {}
                new_info['Url'] = url
                new_info['Cache-Result'] = 'From process'
                new_info['Local-File'] = url

                result_popen = FileInfo(StringIO.StringIO(data), new_info, url)
                return result_popen
            # end if
        # end if

        url = normalizeUrl (url)

        filename = self.checksum(url)        
        info_name = os.path.join(self.location, filename + '.info')
        data_name = os.path.join(self.location, filename + '.data')

        info = self.info(url)

        if info:
            if 'expires' in info.keys():
                t = email.Utils.parsedate(info['Expires'])
                if t:
                    timestamp = datetime(t[0], t[1], t[2], t[3], t[4], t[5])

                    if timestamp < datetime.utcnow():
                        info = None
                    # end if
                # end if
            # end if
        # end if

        if info:
            try:        
                st = os.stat (data_name)
            except OSError:
                st = None
        else:
            st = None
        # end if

        if info and st:
            info['Cache-Result'] = 'Cache hit'
            touchFile (info_name)
            result_cached = FileInfo (open(data_name, 'rb'), info, url)
        else:
            result_cached = None

        if self.offline and result_cached:
            return result_cached
        # end if

        if info and max_age:
            t = email.Utils.parsedate(info['Date'])
            timestamp = datetime(t[0], t[1], t[2], t[3], t[4], t[5])

            if timestamp + timedelta(minutes=max_age) > datetime.utcnow():            
                return result_cached
        # end if

        try:
            new_info = {}
            new_info['Url'] = url
            new_info['Cache-Result'] = 'Downloaded'
            new_info['Local-File'] = url

            result_local = FileInfo(open(url, 'rb'), new_info, url)
            return result_local
        except:
            pass
        # end try

        if self.offline:
            raise OfflineError()
        # end if

        try:
            request = Request(url)
            request.add_header('User-Agent', self.agent)
            request.add_header("Accept-encoding", "gzip")
            if username:
                userpass = (username, password)
                authstring = base64.encodestring('%s:%s' % userpass)[:-1]
                request.add_header("Authorization", "Basic %s" % authstring)
            # end if
            if referer:
                request.add_header('Referer', referer)
            # end if
            if info:
                if 'etag' in info.keys():
                    request.add_header("If-None-Match", info['etag'])
                # end if
                if 'last-modified' in info.keys():
                    request.add_header("If-Modified-Since", info['last-modified'])
                # end if
            # end if

            resource = urlopen (request)
            data = resource.read()

            if resource.headers.get('content-encoding', '') == 'gzip':
                try: 
                    data = gzip.GzipFile(fileobj=StringIO.StringIO(data)).read()
                except:
                    data = resource.read()
            # end if

            info = resource.info()
            info['Url'] = url
            info['Cache-Result'] = 'Downloaded'
            info['Local-File'] = data_name
            dump (info, open(info_name, 'wb'))

            fpout = open(data_name, 'wb')
            fpout.write(data)
            fpout.close()

            result = FileInfo (open(data_name, 'rb'), info, url)
            return result
        except HTTPError, e:
            if e.code == 304 and result_cached:
                result_cached.info['Cache-Result'] = 'No change'
                return result_cached
            else:
                if result_cached:
                    result_cached.info['Cache-Result'] = 'No change'
                    return result_cached
                # end if
                raise
            # end if
        except URLError, e:
            if result_cached:
                result_cached.info['Cache-Result'] = 'URLError (%s), using cache' % e.reason
                return result_cached
            else:
                raise 
            # end if
        except Exception, e:
            if self.debug:
                raise
            # end if

            if result_cached:
                result_cached.info['Cache-Result'] = 'Download error, using cache'
                return result_cached
            else:
                raise 
            # end if
    # end def    

    def content(self):
        result = []
        for x in glob(os.path.join(self.location, '*.info')):
            info = load(open(x, 'rb'))
            result += [info['Url'], ]
        # end for     

        return result
    # end def    

    def info(self, url):
        url = normalizeUrl (url)
        filename = self.checksum(url)        
        info_name = os.path.join(self.location, filename + '.info')
        data_name = os.path.join(self.location, filename + '.data')

        try:
            info = load(open(info_name))

            # if the url stored in "info" is different than the one
            # I'm looking for, then I have a collision of names (due to 
            # the md5 algorithm). Discard the info file, because we don't
            # have a cached version of the url we want
            if info['Url'] != url:
                info = None
            else:
                info['Local-File'] = data_name
            # end if

            if not ('date' in [x.lower() for x in info.keys()]):
                st = os.stat(data_name)
                last_mod = st[8]
                info['Date'] = time.ctime(last_mod)
            # end if
        except:
            info = None
        # end try
        
        return info
    # end def    

    def feed_parse(self, url, can_pipe=False, username=None, password=None):
        if not _has_feedparser:
            import feedparser
        # end if

        resource = self.urlopen(url, can_pipe=can_pipe, username=username, password=password)
        if resource:
            result = parse (resource.content)
            result['channel']['Cache-Result'] = resource.info['Cache-Result']
            return result
        else:
            return None
        # end if
    # end def    

    def purge(self, days=None):
        for x in glob(os.path.join(self.location, '*.info')):
            eliminado = False

            if days:
                try:        
                    st = os.stat (x)
                except OSError:
                    st = None

                if st:
                    timestamp = datetime.fromtimestamp(st[stat.ST_MTIME])
                    delta = timedelta(days=days)
                    if timestamp < datetime.now() - delta:
                        eliminado = True

                        base = os.path.splitext(os.path.split(x)[1])[0]
                        for ext in ['info', 'data']:
                            try:
                                os.remove (os.path.join(self.location, base + '.' + ext))
                            except OSError:
                                pass
                            # end try
                            # end for
                    # end if
                # end if
            # end if
        # end for     
    # end def    

    def getMultiple(self, urls, nWorkers=10, on_before=None, on_after=None, on_error=None, get_list=True):
        class getWorker(_threading.Thread):
            def __init__(self, cache_obj, pendientes, resultados, on_before=None, on_after=None, on_error=None, get_list=True):
                self.pendientes = pendientes
                self.resultados = resultados
                self.cache = cache_obj
                self.on_before = on_before
                self.on_after = on_after
                self.on_error = on_error
                self.get_list = get_list
                _threading.Thread.__init__(self)
            # end def

            def run(self):
                while True:
                    index, url = self.pendientes.get()
                    if url is None:
                        break
                    # end if

                    try:
                        if self.on_before:
                            self.on_before(url)
                        # end if
                        
                        data = self.cache.urlopen(url).content.read()

                        if self.on_after:
                            self.on_after(url, data)
                        # end if
                    except:
                        data = None
                        if self.on_error:
                            self.on_error(url)
                        # end if
                    # end try

                    if self.get_list:
                        self.resultados.put((index, data))                    
                    # end if
                # end while
            # end def    
        # end class

        result = [None,] * urls.__len__()

        pendientes = Queue.Queue(0)
        resultados = Queue.Queue(0)

        workers = []
        for i in range(nWorkers):
            w = getWorker (self, pendientes, resultados, on_before, on_after, on_error, get_list)
            workers += [w,]
            w.start()
        # end for
    
        for i, url in enumerate(urls):
            pendientes.put((i, url))
        # end for

        for i in range(nWorkers):
            pendientes.put((None,None))
        # end for

        while not pendientes.empty():
            time.sleep(0.1)
        # end while

        while not resultados.empty():
            index, data = resultados.get()
            result[index] = data
        # end while

        return result
    # end def    
# end class

if __name__ == '__main__':
    c = Cache(r'C:\Documents and Settings\Administrador\Datos de programa\.newspipe\cache', debug=True, offline=False)
    