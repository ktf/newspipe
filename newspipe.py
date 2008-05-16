#!/usr/bin/env python
# -*- coding: UTF-8 -*-

# $NoKeywords: $   for Visual Sourcesafe, stop replacing tags
__revision__ = "$Revision: 1.66 $"
__revision_number__ = __revision__.split()[1]
__version__ = "1.1.9"
__date__ = "2005-07-17"
__url__ = "http://newspipe.sourceforge.net"
__author__ = "Ricardo M. Reyes <reyesric@ufasta.edu.ar>"
__contributors__ = ["Rui Carmo <http://the.taoofmac.com/space/>", "Bruno Rodrigues <http://www.litux.org/blog/>"]
__id__ = "$Id: newspipe.py,v 1.66 2005/07/18 00:23:28 reyesric Exp $"

ABOUT_NEWSPIPE = """
newspipe.py - version %s revision %s, Copyright (C) 2003-%s \n%s
"""%(__version__, __revision_number__, __date__.split('-')[0], __author__) 

#import psyco
#psyco.full()

import ConfigParser
import md5
from time import sleep, time
import os, sys, os.path
from cache import *
from datetime import datetime, timedelta
from pprint import pprint
from opml import *
from pickle import load, dump
import smtplib
import re
from htmlentitydefs import entitydefs
from difflib import SequenceMatcher
import email.Utils
import email.Header
import Queue
from htmlentitydefs import  *
import MimeWriter
import mimetools
import cStringIO
import base64
import urlparse
import traceback
import sys
import urllib
import urllib2
import logging
import logging.handlers
from urllib2 import URLError
from email import message_from_string
import gc

try:
    import threading as _threading
    has_threading = True
except ImportError:
    import dummy_threading as _threading
    has_threading = False

has_html2text = True
try:
    from html2text import *
except ImportError:
    has_html2text = False

PYTHON_VERSION = '.'.join([str(x) for x in sys.version_info])
USER_AGENT = 'NewsPipe/'+__version__+' rev.'+__revision_number__+' Python: '+ PYTHON_VERSION+' Platform: '+sys.platform +' / '+__url__

OPML_DEFAULTS = {
    'active': '1',
    'digest': '0',
    'titles': '1',
    'download_link': '0',
    'diff': '1',
    'check_text': '1',
    'delay': '60',
    'textonly': '0',
    'mobile': '0',
    'download_images': '1',
    'check_time': '',
    'mobile_time': '',
    'remove': '',
}

CONFIG_DEFAULTS = {
    'textonly': '0',
    'log_console': '0',
    'sleep_time': '5',
    'offline': '0',
    'debug': '0',
    'workers': '10',
    'multipart': 'on',
    'can_pipe': '0',
    'encoding': 'utf-8',
    'proxy': '',
    'threading': '0',
    'subject': '',
    'priority' : '1',
    'smtp_auth' : '0',
    'smtp_user' : '',
    'smtp_pass' : '',
    'smtp_port' : '25',
    'smtp_tls'  : 0,
    'from_address' : '',
    'send_method': 'smtp',
    'procmail': '',
    'reverse' : '0'
}

DEBUG = False

class MyLog:
    debug_memory = 0 # include memory information in debug
    cache = 2        # keep mem stats for "cache" seconds

    h = None         # file handler
    result = None    # memory string
    lasttime = None  # last access to the file
        
    #def die(self): self.h.close()

    def memory(self):
        # /proc/self/status is only available on Linux)
        if self.debug_memory and sys.platform.lower().startswith('linux2'):
            if not self.lasttime:
                self.lasttime = time.time() - self.cache - 1
            if self.lasttime + self.cache >= time.time():
                return self.result
    
            if not self.h:
                self.h=file("/proc/self/status")
            else:
                self.h.seek(0)
            x=self.h.read(1024)
            result = ""
            for l in x.split("\n"):
                if l[0:2] != "Vm": continue
                l = l.replace(" kB", "")
                l = l.replace(" ", "")
                l = l.replace("\t", "")
                l = l.replace(":", ": ")
                result = result + l + ","
            # end for
            if len(result) > 1:
                self.result = result
                result = result[:-1]
            else:
                result = self.result
            result = "[" + result + "] "
            return result
        else:
          return ''
        # end if
    # end def
    
    def debug(self, msg, *args, **kwargs):
        msg = self.memory() + msg
        log.debug(msg, *args, **kwargs)
    def info(self, msg, *args, **kwargs):
        msg = self.memory() + msg
        log.info(msg, *args, **kwargs)
    def warning(self, msg, *args, **kwargs):
        msg = self.memory() + msg
        log.warning(msg, *args, **kwargs)
    def exception(self, msg, *args, **kwargs):
        msg = self.memory() + msg
        log.exception(msg, *args, **kwargs)
    def error(self, msg, *args, **kwargs):
        msg = self.memory() + msg
        log.error(msg, *args, **kwargs)


def LogFile(stderr=True, name='default', location='.', debug=False):
    if not os.path.exists(location):
        os.makedirs(location)

    logger = logging.getLogger(name)
    hdlr = logging.handlers.RotatingFileHandler(os.path.join(location, name+'.log'), maxBytes=1024*500, backupCount=10)
    formatter = logging.Formatter('%(asctime)s %(thread)d %(levelname)-10s %(message)s')
    hdlr.setFormatter(formatter)
    logger.addHandler(hdlr) 

    if stderr:
        hdlr = logging.StreamHandler(sys.stderr)
        hdlr.setFormatter(formatter)
        logger.addHandler(hdlr)
    # end if

    if debug:
        logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.INFO)
    # end if

    return logger
# end def    

def parseTime (text):
    AM = 1
    PM = 2
    UNKNOWN = 3
    
    text = text.lower()
    
    if 'am' in text:
        ampm = AM
        text = text.replace('am', '')
    elif 'pm' in text:
        ampm = PM
        text = text.replace('pm', '')
    else:
        ampm = UNKNOWN
        
    text = text.strip()
    partes = text.split(':')
    if len(partes) == 1:
        partes.append('0')
        
    try:
        hours = int(partes[0])
        minutes = int(partes[1])
    except ValueError:
        return None

    if ampm == PM:
        hours = hours + 12
    
    return (hours, minutes)
    
    return None

def parseTimeRange (text):
    begin, end = None, None
    
    text = text.strip()
    
    separadores = [x for x in (' , ; to = / | -').split(' ') if x]
    separadores.append(' ')
    
    partes = None
    for each in separadores:
        aux = text.split(each)
        if len(aux) == 2:
            partes = aux
    
    if partes:
        partes = [x.strip() for x in partes]
        begin = parseTime(partes[0])
        end = parseTime(partes[1])
        if begin and end:
            return (begin, end)
    
    return None
    
def checkTime (range):
    n = datetime.now()
    hours = n.hour
    minutes = n.minute
    
    begin = range[0][0]*100 + range[0][1]
    end =   range[1][0]*100 + range[1][1]
    current = hours*100 + minutes
    
    if end < begin:
        end += 2400
    
    result = begin <= current <= end
    
    return result

def formatNumber (text):
    i = float(text)
    m = i/(1024*1024)

    if m < 0.01 and m > 0:
        m = 0.01
    return '%0.2f MB' % m


def intEnt(m):
    m = int(m.groups(1)[0])
    return unichr(m)

def xEnt(m):
    m = int(m.groups(1)[0], 16)
    return unichr(m)

def nameEnt(m):
    m = m.groups(1)[0]
    if m in entitydefs.keys():
        return entitydefs[m].decode("latin1")
    else: 
        return "&"+m+";"
    # end if

def expandNumEntities(text):
    text = re.sub(r'&#(\d+);', intEnt, text)
    text = re.sub(r'&#[Xx](\w+);', xEnt, text)
    text = re.sub(r'&(.*?);', nameEnt, text)
    return text

def expandEntities(text):
    text = text.replace("&lt;", "<")
    text = text.replace("&gt;", ">")
    text = text.replace("&quot;", '"')
    text = text.replace("&ob;", "{")
    text = text.replace("&cb;", "}")
    text = text.replace("&middot;", "*")
    text = re.sub("&[rl]squo;", "'", text)
    text = re.sub("&[rl]dquo;", '"', text)
    text = re.sub("&([aeiouAEIOU])(grave|acute|circ|tilde|uml|ring);", lambda m: m.groups(1)[0], text)
    text = re.sub("&([cC])(cedil);", lambda m: m.groups(1)[0], text)
    text = re.sub("&([n])(tilde);", lambda m: m.groups(1)[0], text)
    text = re.sub(r'&#(\d+);', intEnt, text)
    text = re.sub(r'&#[Xx](\w+);', xEnt, text)
    text = re.sub("&(#169|copy);", "(C)", text)
    text = re.sub("&mdash;", "--", text)
    text = re.sub("&amp;", "&", text)
    return text

class TextDiff:
    """Create diffs of text snippets."""

    def __init__(self, source, target):
        """source = source text - target = target text"""
        self.separadores = '"<>'
        self.nl = "<NL>"
        #self.delTag = "<span class='deleted'>%s</span>"
        self.delTag = '<font color="#FF0000"><STRIKE>%s</STRIKE></font>'
        #self.insTag = "<span class='inserted'>%s</span>"
        self.insTag = '<font color="#337700"><b>%s</b></font>'
        self.source = self.SplitHTML(source.replace("\n", "\n%s" % self.nl))
        self.target = self.SplitHTML(target.replace("\n", "\n%s" % self.nl))
        self.deleteCount, self.insertCount, self.replaceCount = 0, 0, 0
        self.diffText = None
        self.cruncher = SequenceMatcher(None, self.source, self.target)
        self._buildDiff()

    def SplitHTML (self, texto):
        version1 = re.compile('(<.+?>)').split(texto)

        version2 = []
        for x in version1:
            if re.compile('<.+>').search(x):
                version2 += [x,]
            else:
                version2 += x.split()
            # end if
        # end for
        return version2

    def _buildDiff(self):
        """Create a tagged diff."""
        outputList = []
        for tag, alo, ahi, blo, bhi in self.cruncher.get_opcodes():
            if tag == 'replace':
                # Text replaced = deletion + insertion
                outputList.append(self.delTag % " ".join(self.source[alo:ahi]))
                outputList.append(self.insTag % " ".join(self.target[blo:bhi]))
                self.replaceCount += 1
            elif tag == 'delete':
                # Text deleted
                outputList.append(self.delTag % " ".join(self.source[alo:ahi]))
                self.deleteCount += 1
            elif tag == 'insert':
                # Text inserted
                outputList.append(self.insTag % " ".join(self.target[blo:bhi]))
                self.insertCount += 1
            elif tag == 'equal':
                # No change
                outputList.append(" ".join(self.source[alo:ahi]))
        diffText = " ".join(outputList)
        diffText = " ".join(diffText.split())
        self.diffText = diffText.replace(self.nl, "\n")

    def getStats(self):
        "Return a tuple of stat values."
        return (self.insertCount, self.deleteCount, self.replaceCount)

    def getDiff(self):
        "Return the diff text."
        aux = self.diffText
        return aux

def createhtmlmail (html, text, headers, images=None, rss_feed=None, link=None, encoding='utf-8'):
    """Create a mime-message that will render HTML in popular
    MUAs, text in better ones"""

    global cache, log

    if not isinstance(text, unicode):
        text = text.decode('latin1')
    # end if
    if isinstance(text, unicode):
        text = text.encode('utf-8')
    # end if
    
    if not isinstance(html, unicode):
        html = html.decode('latin1')
    # end if
    if isinstance(html, unicode):
        html = html.encode('utf-8')
    # end if
    
    out = cStringIO.StringIO() # output buffer for our message
    htmlin = cStringIO.StringIO(html)
    txtin = cStringIO.StringIO(text)
    if rss_feed:
        rssin = cStringIO.StringIO(rss_feed)
    # end if

    writer = MimeWriter.MimeWriter(out)
    #
    # set up some basic headers... we put subject here
    # because smtplib.sendmail expects it to be in the
    # message body
    #

    for x,y in headers:
        writer.addheader(x, y.encode('utf-8'))

    writer.addheader("MIME-Version", "1.0")
    #
    # start the multipart section of the message
    # multipart/alternative seems to work better
    # on some MUAs than multipart/mixed
    #
    writer.startmultipartbody("alternative")
    writer.flushheaders()
    
    #
    # the plain text section
    #
    if(text != ""):
        subpart = writer.nextpart()
        subpart.addheader("Content-Transfer-Encoding", "quoted-printable")
        pout = subpart.startbody("text/plain", [("charset", 'utf-8'), ("delsp", 'yes'), ("format", 'flowed')])
        mimetools.encode(txtin, pout, 'quoted-printable')
        pout.write (txtin.read())
        txtin.close()
    
    #
    # start the html subpart of the message
    #
    if images:
        htmlpart = writer.nextpart()
        htmlpart.startmultipartbody("related")
        subpart = htmlpart.nextpart()
    else:
        subpart = writer.nextpart()
    subpart.addheader("Content-Transfer-Encoding", "quoted-printable")
    #
    # returns us a file-ish object we can write to
    #
    pout = subpart.startbody("text/html", [("charset", 'utf-8')])
    mimetools.encode(htmlin, pout, 'quoted-printable')
    htmlin.close()

    if images:
        for x in images:
            try:
                ext = 'gif'
                ruta, archivo = os.path.split(x['url'])
                if archivo:
                    name, ext = os.path.splitext(archivo)
                    if ext:
                        ext = ext[1:]

                        if '?' in ext:
                            ext = ext[:ext.find('?')]
                        # end if
                    # end if
                # end if
                
                if link:
                    # if the url is relative, then add the link url to form an absolute address
                    url_parts = urlparse.urlsplit(x['url'])
                    if not url_parts[1]:
                        if not url_parts[0].upper() == 'FILE:':
                            x['url'] = urlparse.urljoin(link, x['url'])
                        # end if
                    # end if
                # end if
                x['url'] = x['url'].replace(' ', '%20')
            
                retries = 0;
                MAX_RETRIES = 3;
                img_referer = link
                resource = None
                while retries < MAX_RETRIES:
                    retries += 1

                    # try to fetch the image.
                    # in case of Timeout or URLError exceptions, retry up to 3 times
                    try:
                        resource = cache.urlopen(x['url'], max_age=999999, referer=img_referer, can_pipe=False)
                    except HTTPError, e:
                        # in case of HTTP error 403 ("Forbiden") retry without the Referer
                        if e.code == 403 and img_referer:
                            mylog.info ('HTTP error 403 downloading %s, retrying without the referer' % (x['url'],))
                            img_referer = None
                        else:
                            raise
                        # end if
                    except (socket.timeout, socket.error):
                        mylog.info ('Timeout error downloading %s' % (x['url'],))
                        if retries == MAX_RETRIES:
                            raise
                        # end if
                    except URLError, e:
                        mylog.info ('URLError (%s) downloading %s' % (e.reason, x['url'],))
                        if retries == MAX_RETRIES:
                            raise
                        # end if
                    except Exception:
                        raise # any other exception, kick it up, to be handled later
                    else:
                        # if there's no exception, break the loop to continue 
                        # processing the image
                        break
                    # end try
                            
                    mylog.info ('Retrying, %d time' % retries);
                # end while

                if not resource:
                    raise Exception('Unknown problem')
                # end if

                explicacion = resource.info['Cache-Result']

                mylog.debug (explicacion + ' ' + x['url'])

                info = resource.info
                content_type = info['Content-Type']
                # end if

                subpart = htmlpart.nextpart()
                subpart.addheader("Content-Transfer-Encoding", "base64")
                subpart.addheader("Content-ID", "<" + x['name'] + ">")
                subpart.addheader("Content-Location", x['name'])
                subpart.addheader("Content-Disposition", "inline; filename=\"" +x['filename'] + "\"" )
                f = subpart.startbody(content_type, [["name", x['name']]])
                b64 = base64.encodestring(resource.content.read())
                f.write(b64)
                image_ok = True  # the image was downloaded ok
            except KeyboardInterrupt:
                raise
            except socket.timeout:
                mylog.info ('Timeout error downloading %s' % (x['url'],))
                image_ok = False
            except HTTPError, e:
                mylog.info ('HTTP Error %d downloading %s' % (e.code, x['url'],))
                image_ok = False
            except URLError, e:
                mylog.info ('URLError (%s) downloading %s' % (e.reason, x['url'],))
                image_ok = False
            except OfflineError:
                mylog.info ('Resource unavailable when offline (%s)' % x['url'])
                image_ok = False
            except Exception, e:
                mylog.exception ('Error %s downloading %s' % (str(e), x['url'],))
                image_ok = False
            # end try
            if not image_ok:
                x['url'] = 'ERROR '+x['url'] # arruino la url para que no se reemplace en el html
            # end if
        # end for
        htmlpart.lastpart()
    # end if
    
    #
    # the feed section
    #

    if rss_feed:
        subpart = writer.nextpart()
        subpart.addheader("Content-Transfer-Encoding", "quoted-printable")
        pout = subpart.startbody("text/plain", [("charset", 'us-ascii'), ("Name", "rss_feed.xml")])
        mimetools.encode(rssin, pout, 'quoted-printable')
        rssin.close()
    # end if

    #
    # Now that we're done, close our writer and
    # return the message body
    #
    writer.lastpart()
    msg_source = out.getvalue()
    out.close()
    return message_from_string (msg_source.encode(encoding, 'replace'))

def createTextEmail(text, headers, encoding='utf-8'):
    t = '\r\n'.join([x+': '+y for x,y in headers])
    t += '\r\n\r\n'
    t += text
    return message_from_string(t.encode(encoding, 'replace'))
# end def    


def quitarEntitys (text):   
    return re.sub(r'(&\D+?;)', '', text)


class Channel:
    def __init__(self, title, original, xmlUrl, htmlUrl, download_link, diff, download_images, parameters):
        self.original = original
        self.xmlUrl = xmlUrl
        self.htmlUrl = htmlUrl
        self.title = original.get('title', title)
        self.description = original.get('description', self.title)
        self.creator = original.get('creator', original.get('author', self.title))
        self.download_link = download_link
        self.download_images = download_images
        self.diff = diff
        self.parameters = parameters

    def NewItem(self, original, encoding="utf-8", remove=None):
        return Item(original, self, encoding, remove)
    # end def
# end class

def item_checksum(item):
    """ Calculates the MD5 checksum of an rss item """
    m = md5.new()
    for x in item.values():
        m.update (str(x))
    # end for
    return m.hexdigest()
# end def




historico_posts = {}
historico_feeds = {}


def getEntity(m):
    v = int(m.groups(1)[0])
    if v in codepoint2name.keys():
        return '&'+codepoint2name[v]+';'
    else:
        return ''

def SanitizeText (text):

    text = text.replace('\n', ' ')
    
    entitys = entitydefs
    inverso = {}
    for i,j in entitys.items():
        inverso[j] = '&'+i+';'

    chars = filter(lambda x: ord(x) >= 128, text)
    if chars:
        for c in chars:
            if inverso.has_key(c):
                text = text.replace(c, inverso[c])
            else:
                text = text.replace(c, '')
    

    text = re.sub(r'&#(\d+);', getEntity, text)
    return text


def GetValue (x):
    if isinstance(x, basestring):
        return x
    elif isinstance(x, list):
        try:
            return x[0]['value']
        except:
            return ''
    else:
        return ''


entitydefs2 = {}
for key,value in entitydefs.items():
    entitydefs2[value] = key
# end for

def corregirEntitys(texto):
    '''This function replaces special characters with &entities; '''
    if not texto:
        return texto
    # end if

    if not isinstance(texto, unicode):
        texto = texto.decode('latin1')

    result = ''
    for c in texto:
        if not (c in ('<', '>', '/', '"', "'", '=', '&')):
            if c.encode("latin1", 'replace') in entitydefs2.keys():
                rep = entitydefs2[c.encode("latin1", "replace")]
                rep = '&'+rep+';'
                result += rep
            else:
                result += c
            # end if
        else:
            result += c
        # end if
    # end for

    return result
# end def



def getException():
    return '\n'.join(traceback.format_exception (sys.exc_info()[0], sys.exc_info()[1], sys.exc_info()[2]))


semaforo_html2text = _threading.BoundedSemaphore()


def makeHeader(text):
    if not text:
        text = ''
    
    if not isinstance(text, unicode):
        text = text.decode('latin1')
    # end if

    if isinstance(text, unicode):
        text = text.encode('utf-8')
    # end if
    
    try:
        if has_html2text:
            text = html2text(text).strip()
    except UnicodeError:
        pass

    return str(email.Header.make_header([(text, 'utf-8')]))
# end def    


def getPlainText(html, links=True):
    if not isinstance(html, unicode):
        html = html.decode('latin1')
    # end if
    plain_text = u''
    if has_html2text:
        # html2text seems to be not-thread-safe, so I'm avoiding concurrency
        # here using a semaphore
        semaforo_html2text.acquire()
        try:
            try:
                plain_text = html2text(html).strip()
            except:
                plain_text = getException ()
                mylog.exception ('Error en getPlainText')
            # end try
        finally:
            semaforo_html2text.release()
        # end try
    # end if

    if not isinstance(plain_text, unicode):
        plain_text = plain_text.decode('utf-8')
    # end if

    return plain_text
# end def    

def md5texto(texto):
    m = md5.new()
    m.update (texto)
    return m.hexdigest()
# end def    


class Item:
    def __init__(self, original, channel, encoding="utf-8", remove=None):
        global historico_posts

        if encoding == '': encoding="utf-8"

        for key in original.keys():
            if type(original.get(key)) == type(""):
                original[key] = original[key].decode(encoding, "replace")
            # end if
        # end for

        self.original = original
        self.link = GetValue(original.get('link', channel.htmlUrl))
        if original.has_key('enclosures'):
            self.enclosures = original.enclosures
        else:
            self.enclosures = ()
        # end if

        self.texto_nuevo = ''
        self.text_key = 'None'
        for k in 'content body content_encoded description summary summary_detail'.split():
            if k in original.keys():
                if original[k]:
                    self.texto_nuevo = original[k]
                    self.text_key = k
                    break
                # end if
            # end if
        # end for
        if self.text_key == None and 'summary_detail' in original.keys() and 'value' in original['summary_detail'].keys():
            self.texto_nuevo = original['summary_detail']['value']
            self.text_key = "summary_detail/value"
        # end if

        self.texto_nuevo = GetValue (self.texto_nuevo)

        if channel.download_link:
            try:
                downloaded_file = cache.urlopen(self.link, max_age=999999, can_pipe=False);
                explicacion = downloaded_file.info['Cache-Result']
                mylog.debug (explicacion + ' ' + self.link)
            except KeyboardInterrupt:
                raise
            except:
                mylog.exception ('Cannot download '+self.link)
                downloaded_file = None
            # end try

            if downloaded_file:
                self.texto_nuevo = downloaded_file.content.read()
            # end if
        # end if
        
        if remove:
            rc = re.compile (remove, re.I+re.S+re.X)
            self.texto_nuevo = re.sub(rc, '', self.texto_nuevo)

        if type(self.texto_nuevo) == type(""):
            try:
                self.texto_nuevo = self.texto_nuevo.decode(encoding)
            except UnicodeDecodeError, e:
                mylog.debug("Error in " + channel.xmlUrl + ", " + original.get('title', original.get('url', '?')) + ": " + str(e))
                self.texto_nuevo = self.texto_nuevo.decode(encoding, 'replace')
            # end try
        # end if
        self.texto_nuevo = corregirEntitys(self.texto_nuevo)
        self.subject = GetValue (original.get('title', ''))

        if not self.subject:
            sin_html = ' '.join(re.compile('<.+?>').split(self.texto_nuevo))

            self.subject = sin_html[:60].strip()

            if '\n' in self.subject:
                self.subject = self.subject.split('\n')[0]
            # end if
            self.subject += '...'
        # end if

        m = md5.new()
        m.update (self.link.encode('utf-8', 'replace'))
        m.update (channel.xmlUrl)
        m.update (self.subject.encode('utf-8', 'replace'))
        self.urlHash = m.hexdigest()
        
        self.subject = self.subject

        if 'modified_parsed' in original.keys() and original['modified_parsed'] != None:
            x = original['modified_parsed']
            self.timestamp = datetime(year=x[0], month=x[1], day=x[2], hour=x[3], minute=x[4], second=x[5])
        else:
            self.timestamp = datetime.now()
        # end if

        self.texto = self.texto_nuevo
        if channel.diff and historico_posts.has_key(self.urlHash):
            before_diff = self.texto_nuevo
            differ = TextDiff(historico_posts[self.urlHash]['text'], self.texto_nuevo)
           
            self.texto = differ.getDiff()
            if self.texto <> before_diff:
                self.timestamp = datetime.now()
        # end if
        
        self.channel = channel

        self.creatorName = GetValue(original.get('creator', original.get('author', channel.creator)))
        # set the default From: address to "rss@domain" where domain comes from the site's url
        self.creatorEmail = 'rss@'+ urlparse.urlparse(channel.htmlUrl)[1] 

        # search for an email address, in the item first, then in the channel
        r = re.compile('([A-Za-z0-9_.\+]+@[A-Za-z0-9_.]+)')
        for x in [original.get('creator', ''), original.get('author', ''), channel.creator]:
            try:
                m = r.search(x)
                if m:
                    self.creatorEmail = m.group(1)
            except TypeError:
                pass
              
        self.is_modified = 'Unknown'
        
        self.custom_tags = {}
        known_tags = ['text', 'link', 'htmlUrl', 'xmlUrl', 'description', 'path', 'title', 'index'] + OPML_DEFAULTS.keys()
        for k in channel.parameters.keys():
            if not k in known_tags:
                self.custom_tags[k] = channel.parameters[k]

    def __repr__(self):
        #return 'Link: %s\nTimeStamp: %s\nTexto: %s' % (self.link, self.timestamp, self.texto)
        return self.subject
        #return self.original.__repr__()
    # end def

    def GetEmail(self, envio, destinatario, format="multipart", encoding='utf-8', include_threading=False, subject_prefix=None, from_address=None):
        global historico_posts
        template = """
<font face="Arial,Helvetica,Geneva">
    <p>
        __body__
    </p>
    <hr />
    <p>
        <a href="__htmlUrl__">Home</a>
        &nbsp;&nbsp;&nbsp;
        <a href="__permalink__">Link</a>
        &nbsp;&nbsp;&nbsp;
        __enclosure__
    </p>
</font>
"""
        #self.texto = expandNumEntities(self.texto)

        body = self.texto
        text_version = getPlainText (body)
        text_version = text_version + "\n\n" + "Home: [" + self.channel.htmlUrl + "]\n" + "Link: [ " + self.link + " ]\n"
        
        if self.enclosures:
            for enclosure in self.enclosures:
                text_version = text_version + "Enclosure: [ " + enclosure.get('url') + "  (" + formatNumber(enclosure.get('length', '0')) + ") ]\n"
            # end for
        # end if

        html_version = template
        html_version = html_version.replace('__subject__', self.subject)
        html_version = html_version.replace('__body__', body)
        html_version = html_version.replace('__permalink__', self.link)
        html_version = html_version.replace('__htmlUrl__', self.channel.htmlUrl)
        
        enclosure_text = ""
        if self.enclosures:
            for enclosure in self.enclosures:
                enclosure_text = enclosure_text + "<a href=\"" + enclosure.get('url') + "\"> Enclosure (" + formatNumber(enclosure.get('length', '0')) + ")</a>&nbsp;&nbsp;&nbsp;"
            # end for
        #ed if
                
        html_version = html_version.replace('__enclosure__', enclosure_text)
        
        img_search_re = re.compile('<.*?img.+?src.*?=.*?[\'"](.*?)[\'"]', re.IGNORECASE)
        
        # edit all the image urls that are relative to make them fully qualified
        if self.link:
            urls = re.findall(img_search_re, html_version)
            for url in urls:
                url_parts = urlparse.urlsplit(url)
                if not url_parts[1]:
                    if not url_parts[0].upper() == 'FILE:':
                        full_url = urlparse.urljoin(self.link, url)
                        html_version = html_version.replace (url, full_url)
                    # end if
                # end if
        # end if

        images = None
        if format != "plaintext" and self.channel.download_images:
            urls = re.findall(img_search_re, html_version)
            if urls:
                images = []
                seenurls = []
                i = 0
                for url in urls:
                    if url:
                        # check if this url was already proccesed
                        previous = [x['url'] for x in images]
                        if not (url in previous):
                            filename = os.path.basename(url)
                            if '?' in filename:
                                filename = filename[:filename.find('?')]
                            ext = os.path.splitext(url)[1]
                            if '?' in ext:
                                ext = ext[:ext.find('?')]
                            # end if
                            name = '%s%s' % (md5texto(filename+str(i)),ext)
                            html_version = html_version.replace(url, 'cid:'+name)
                            images += [{'name':name, 'url':url, 'filename':filename},]
                            i += 1
                        # end if
                    # end if
                # end for
                seenurls = None
            # end if
        # end if

        envio = self.creatorEmail
        if envio == None:
            envio = destinatario[1]
        # end if
        
        if subject_prefix:
            subject = subject_prefix + ': ' + self.subject
        else:
            subject = self.subject
            
        to_header = ', '.join(['"%s" <%s>"' % (destinatario[0], each.strip()) for each in destinatario[1].split(',')])
        if from_address:
            from_header = from_address
        else:
            from_header = '"%s" <%s>' % (makeHeader(self.channel.title), envio)

        headers = []
        headers += [('From', from_header),]
        headers += [('To', to_header),]
        headers += [('Subject', makeHeader(subject)),]
        msgid = email.Utils.make_msgid()
        headers += [('Message-ID', msgid),]
        headers += [('Date', self.timestamp.strftime("%a, %d %b %Y %H:%M:%S +0000")),]

        headers += [('X-NewsPipe-Version', '%s (Rev %s, Python %s, %s) %s' % (__version__, __revision_number__, PYTHON_VERSION, sys.platform, __url__)),]
        headers += [('X-Channel-Feed', self.channel.xmlUrl),]
        headers += [('X-Channel-title', makeHeader(self.channel.title)),]
        headers += [('X-Channel-description', makeHeader(self.channel.description)),]
        headers += [('List-Id', '%s <%s>' % ( makeHeader(self.channel.title), self.channel.xmlUrl)),]
        headers += [('Content-Location', self.link),]
        
        for k in self.custom_tags.keys():
            headers += [('X-Custom-'+k, makeHeader(self.custom_tags[k])),]

        if DEBUG:
            headers += [('X-Channel-x-cache-result', self.channel.original['Cache-Result']),]
            headers += [('X-Item-Attributes', ', '.join(self.original.keys())),]
            headers += [('X-Item-Text-Key', self.text_key),]
            headers += [('X-Item-Modified', self.is_modified),]
            headers += [('X-Item-Hash-Link', md5texto(self.link.encode('latin1', 'replace'))),]
            headers += [('X-Item-Hash-Feed', md5texto(self.channel.xmlUrl.encode('latin1', 'replace'))),]
            headers += [('X-Item-Hash-Subject', md5texto(self.subject.encode('latin1', 'replace'))),]
            headers += [('X-Item-Hash', self.urlHash),]
            if images:
                for each in images:
                    headers.append (('X-Image-'+each['name'], each['url']))
       
        lastid = historico_feeds[self.channel.xmlUrl].get("lastid", "")
        if lastid == "":
            m = md5.new()
            m.update (self.channel.xmlUrl)
            refid = "<" + m.hexdigest() + "@rss.example.com>"
            lastid = refid
        else:
            refid = lastid.split()[-1]
        # endif
       
        if include_threading:      
            headers += [('In-Reply-To', refid),]
            headers += [('References', lastid),]
 
        if historico_feeds[self.channel.xmlUrl].has_key("lastid"):
            historico_feeds[self.channel.xmlUrl]["lastid"] = " ".join( (historico_feeds[self.channel.xmlUrl]["lastid"] + " " + msgid).split()[-4:] )
        else:
            historico_feeds[self.channel.xmlUrl]["lastid"] = refid + " " + msgid
        historico_feeds["modified"]=True
 
        if format == "plaintext":
            return createTextEmail (text_version, headers, encoding)
        else:
            if( format == "html" ):
                return createhtmlmail (html_version, '', headers, images, None, self.link, encoding)
            else: # multipart
                return createhtmlmail (html_version, text_version, headers, images, None, self.link, encoding)
        # end if
    # end def
# end class



def LeerConfig():
    from optparse import OptionParser

    parser = OptionParser()
    parser.add_option("-i", "--inifile", dest="inifile", help=".ini file with the configuration")
    parser.add_option("-o", "--opml", dest="opml", help="the filename or URL of the OPML file with the list of feeds to check")
    parser.add_option("-s", "--smtp_server", dest="smtp_server", help="fully qualified domain name or IP address of the SMTP server to send messages through")
    parser.add_option("-e", "--sender", dest="sender", help="optional e-mail address to use as From: - overrides the OPML ownerEmail field.")
    parser.add_option("-t", "--textonly", action="store_const", const="1", dest="textonly", help=" all the messages sent by newspipe will be sent in plaintext format, without any HTML")
    parser.add_option("-l", "--log_console", action="store_const", const="1", dest="log_console", help="send logging output to the console and to the log file.")
    parser.add_option("-c", "--check_online", dest="check_online", help="URL of a webpage that the program will try to fetch to determine if there is a network connection available")
    parser.add_option("-d", "--sleep_time", dest="sleep_time", help="Number of minutes to wait before re-checking feeds")
    parser.add_option("-b", "--batch", action="store_const", const="0", dest="sleep_time", help="process all feeds and exit inmediatly")
    parser.add_option("-f", "--offline", action="store_const", const="1", dest="offline", help="the program won't try to fetch any data from the internet, using cached versions instead")
    parser.add_option("-x", "--debug", action="store_const", const="1", dest="debug", help="log a lot of debug information")
    parser.add_option("-w", "--workers", dest="workers", help="Number of threads to use simultaneusly")
    parser.add_option("-m", "--multipart", action="store_const", const="on", dest="multipart", help=" include a plaintext version of item contents as well as an HTML version.")
    parser.add_option("-p", "--can_pipe", action="store_const", const="1", dest="can_pipe", help="Allow the pipe:// protocol in urls")
    parser.add_option("-u", "--encoding", dest="encoding", help="unicode encoding to use when composing the emails")
    parser.add_option("-r", "--proxy", dest="proxy", help="addess and port of the proxy server to use")
    parser.add_option("-a", "--threading", action="store_const", const="1", dest="threading", help="include threading headers in the emails")
    parser.add_option("", "--subject", dest="subject", help="add a fixed text to the subject of every message")
    parser.add_option("", "--smtp_authentication", action="store_const", const="1", dest="smtp_auth", help="authenticate with SMTP server")
    parser.add_option("", "--smtp_auth_user", dest="smtp_user", help="SMTP username used for authentication")
    parser.add_option("", "--smtp_auth_pass", dest="smtp_pass", help="SMTP password used for authentication")
    parser.add_option("", "--smtp_port", dest="smtp_port", help="TCP port on which the SMTP server listen")
    parser.add_option("", "--smtp_tls", action="store_const", const="1", dest="smtp_tls", help="SMTP server uses TLS")
    parser.add_option("", "--send_method", dest="send_method", help="Method used to send the resulting emails. Possible values: SMTP, PROCMAIL, BOTH")
    parser.add_option("", "--procmail", dest="procmail", help="Path of the procmail script, used when SEND_METHOD=PROCMAIL or BOTH")
    parser.add_option("", "--reverse", action="store_const", const="1", dest="reverse", help="reverse the order of emails as they are sent")

    
    (options, args) = parser.parse_args()
    
    if options.inifile:
        inifile = options.inifile
    else:
        source_path = os.path.split(sys.argv[0])[0]
    
        for p in ('.', source_path):
            inifile = os.path.join(p, 'newspipe.ini')
            if os.path.exists(inifile):
                break

    if not os.path.exists(inifile):
        raise ValueError ("Can't find the ini file at "+inifile)

    ini = ConfigParser.ConfigParser()
    ini.read(inifile)

    result = {}
    for attr in ini.options('NewsPipe'):
        result[attr.lower()] = ini.get('NewsPipe', attr)
    # end for
    
    for key, value in CONFIG_DEFAULTS.items():
        if not key in result.keys():
            result[key] = value
            
    for key in [x.dest for x in parser.option_list]:
        if key:
            value = getattr(options, key)
            if value:
                result[key] = value
    
    if result['proxy']:    
        if not '://' in result['proxy']:
            result['proxy'] = 'http://' + result['proxy']
        proxy_support = urllib2.ProxyHandler({"http":result['proxy']})
        opener = urllib2.build_opener(proxy_support)
        urllib2.install_opener(opener)
        
    if not (result['send_method'].lower() in ('smtp', 'procmail', 'both')):
        raise ValueError ('The value of the parameter SEND_METHOD must be SMTP, PROCMAIL or BOTH')
            
    return result
# end def

def EnviarEmails(msgs, method, server, auth, auth_user, auth_pass, procmail, reverse, port, tls, sender):
    if msgs:
        if reverse:
            msgs.reverse()
        
        if method.lower() in ('smtp', 'both'):
            smtp = smtplib.SMTP(server, port)
            if tls:
                smtp.ehlo()
                smtp.starttls()
                smtp.ehlo()
            # authenticate with SMTP server when there's need to
            if auth:
                smtp.login(auth_user,auth_pass);
    
            smtp.set_debuglevel(0)
    
            count = 0;
            for msg in msgs:
                if msg == None: 
                    continue
    
                fromaddr = sender
    
                r = re.compile('<(.+?)>')
                toaddr = r.findall(msg['To'])
    
                try:
                    # build envelope and send message
                    smtp.sendmail(fromaddr, toaddr, msg.as_string(unixfrom=False))
                    count = count + 1
                    mylog.debug('mail sent to %s from %s ' % (toaddr, fromaddr))
                except smtplib.SMTPDataError, e:
                    mylog.warning("Error sending mail ("+str(e)+")")
                    mylog.warning(msg)
                except socket.timeout:
                    sleep(3)
                    smtp.sendmail(fromaddr, toaddr, msg)
                # end try
    
                if count % 10 == 0:
                    # close the connection and reconnect every 10 messages
                    smtp.rset()
                    smtp.quit()
                    smtp = smtplib.SMTP(server, port)
                    if tls:
                        smtp.ehlo()
                        smtp.starttls()
                        smtp.ehlo()
                    # authenticate with SMTP server when there's need to
                    if auth:
                        smtp.login(auth_user,auth_pass);
                    # end if
                # end if
            # end for

            smtp.rset()
            smtp.quit()
            if count != len(msgs):
                note = " (" + str(len(msgs)-count) +" failed)"
            else: 
                note=""
            mylog.info ('%d emails sent successfully%s via SMTP' % (count,note,))
        # end if
        
        if method.lower() in ('procmail', 'both'):
            count = 0
            for msg in msgs:
                try:
                    fp = os.popen(procmail, 'w')
                    fp.write(msg.as_string(unixfrom=True))
                    status = fp.close()
                except IOError:
                    mylog.error ('IOError executing '+procmail)
                    status = 1
                
                if status is None:
                    count += 1
                # end if
            # end for
            if count != len(msgs):
                note = " (" + str(len(msgs)-count) +" failed)"
            else: 
                note=""
            mylog.info ('%d emails sent successfully%s via PROCMAIL' % (count,note,))
        # end if
    # end if
# end def

def AgruparItems(lista, titles, encoding, reverse):
    def cmpItems(x,y):
        if ('modified_parsed' in x.original.keys()) and (x.original['modified_parsed']):
            aux = x.original['modified_parsed']
            tsx = datetime(year=aux[0], month=aux[1], day=aux[2], hour=aux[3], minute=aux[4], second=aux[5])
        else:
            tsx = datetime.now()
        # end if

        if ('modified_parsed' in y.original.keys()) and (y.original['modified_parsed']):
            aux = y.original['modified_parsed']
            tsy = datetime(year=aux[0], month=aux[1], day=aux[2], hour=aux[3], minute=aux[4], second=aux[5])
        else:
            tsy = datetime.now()
        # end if

        return cmp(tsy,tsx)
    # end def    

    lista.sort (cmpItems)
    if reverse:
        lista.reverse()

    template1 = """
<font face="Arial,Helvetica,Geneva">
    <p>
        <font size=+1>
            <strong>
                <a href="__permalink__">
                    __subject__
                </a>
            </strong>
        </font>
        <br>
        <strong>
            by __creator__
        </strong>
        , __timestamp__
    </p>
    <p>
        __body__
    </p>
    __enclosure__
</font>
<br clear=all />
<hr />
"""

    template2 = """
<font face="Arial,Helvetica,Geneva">
    <p>
       <a href="__permalink__">#</a>&nbsp;
        __body__
    </p>
</font>
"""

    texto = ''

    for item in lista:
        if titles:
            html_version = template1
        else:
            html_version = template2
        # end if
        html_version = html_version.replace('__permalink__', item.link)
        html_version = html_version.replace('__subject__', item.subject)
        html_version = html_version.replace('__body__', item.texto)
        html_version = html_version.replace('__creator__', '<a href="mailto:%s">%s</a>' % (item.creatorEmail, item.creatorName))
        html_version = html_version.replace('__timestamp__', item.timestamp.strftime("%a, %d %b %Y %H:%M:%S +0000"))

        enclosure_text = ""
        if item.enclosures:
            for enclosure in item.enclosures:
                enclosure_text = enclosure_text + "<a href=\"" + enclosure.get('url') + "\"> Enclosure (" + formatNumber(enclosure.get('length', '0')) + ")</a>&nbsp;&nbsp;&nbsp;"
            # end for
        #ed if
                
        html_version = html_version.replace('__enclosure__', '<p>'+enclosure_text+'</p>')
        
        texto += html_version
    # end for
    dicc = {}
    dicc['body'] = texto
    dicc['title'] = '%s (%d items)' % (lista[0].channel.title, lista.__len__())
    dicc['link'] = lista[0].channel.htmlUrl
    if 'modified_parsed' in lista[0].original.keys():
        dicc['modified_parsed'] = lista[0].original['modified_parsed']
    # end if
    
    customs = {}
    for each in lista:
        for k, v in each.custom_tags.items():
            if k in customs.keys():
                if not v in customs[k]:
                    customs[k] += ' '+ v
            else:
                customs[k] = v
                
    for k,v in customs.items():
        dicc[k] = v

    return lista[0].channel.NewItem(dicc, encoding)
# end def



def CargarHistoricos(name):
    if isinstance(name, unicode):
        name = name.encode('latin1', 'replace')
    
    data_dir = os.path.normpath(os.path.join(GetHomeDir(), '.newspipe/data'))

    if not os.path.exists(data_dir):
        os.makedirs(data_dir)

    try:
        if historico_feeds:
            del(historico_feeds)
        # end if
    except UnboundLocalError: 
        pass

    try:
        file_name = os.path.join(data_dir, name+'.feeds')
        historico_feeds = load(open(file_name))
        mylog.debug('Loading feed archive '+name+'.feeds')
    except:
        try:
            mylog.debug('Archive not found. Trying backup file '+name+'.feeds.bak')
            file_name = os.path.join(data_dir, name+'.feeds.bak')
            historico_feeds = load(open(file_name))
        except:
            historico_feeds = {}

    try:
        if historico_posts:
            del(historico_posts)
        # end if
    except UnboundLocalError: 
        pass

    try:
        file_name = os.path.join(data_dir, name+'.posts')
        mylog.debug('Loading post archive '+name+'.posts')
        historico_posts = load(open(file_name))
    except:
        try:
            mylog.debug('Archive not found. Trying backup file '+name+'.posts.bak')
            file_name = os.path.join(data_dir, name+'.posts.bak')
            historico_posts = load(open(file_name))
        except:
            historico_posts = {}

    historico_feeds['modified'] = False
    historico_posts['modified'] = False

    return historico_feeds, historico_posts
# end def


def GrabarHistorico(dicc, name, extension):
    if isinstance(name, unicode):
        name = name.encode('latin1', 'replace')
        
    data_dir = os.path.normpath(os.path.join(GetHomeDir(), '.newspipe/data'))
    
    mylog.debug('Saving archive '+name+extension)
    dump(dicc, open(os.path.join(data_dir, name + extension +'.new'), 'w'))

    try: os.remove (os.path.join(data_dir, name+extension+'.bak'))
    except OSError: pass
    try: os.rename (os.path.join(data_dir, name+extension), os.path.join(data_dir, name+extension+'.bak'))
    except OSError: pass

    os.rename (os.path.join(data_dir, name+extension+'.new'), os.path.join(data_dir, name+extension))
    dicc['modified'] = False



def CheckOnline(config):
    if config.has_key('check_online'):
        url = config['check_online']
        try:
            mylog.debug ('Checking online status (downloading '+url+')')
            urllib2.urlopen(url)
            mylog.debug ('Status: online')
            return True
        except:
            mylog.debug ('Status: offline')
            return False
    else:
        return True

def GetHomeDir():
    """ Returns the home directory of the current user."""
    
    for name in ('appdata', 'HOME'):
        result = os.environ.get(name, None)
        if result:
            return result
        # end if
    # end for

    # if it can't find the home directory trough environment vars, then 
    # return the path to this script.
    return os.path.split(sys.argv[0])[0]
# end def    

class FeedWorker (_threading.Thread):
    def __init__(self, feeds_queue, email_queue, config, email_destino, movil_destino, semaforo):
        self.config = config
        self.email_destino = email_destino
        self.movil_destino = movil_destino
        self.semaforo = semaforo

        self.feeds_queue = feeds_queue
        self.email_queue = email_queue

        _threading.Thread.__init__(self)
    # end def

    def run(self):
        config = self.config
        _email_destino = self.email_destino
        movil_destino = self.movil_destino
        semaforo = self.semaforo

        while True:
            gc.collect()
            feed = self.feeds_queue.get()
            if feed is None:
                break
            # end if
            
            url = feed['xmlUrl']
            try:
                time = feed.get('check_time', None)
                if time:
                    parsed_time = parseTimeRange(time)
                    if parsed_time:
                        if not checkTime (parsed_time):
                            mylog.debug ('Ignoring the feed '+url)
                            continue
                    else:
                        mylog.error ('Error parsing the time range "%s" in the feed %s' % (time, url))

                items = []

                semaforo.acquire()
                if not historico_feeds.has_key(url):
                    historico_feeds[url] = {}
                    historico_feeds[url]['ultimo_check'] = None
                    historico_feeds[url]['proximo_check'] = None
                    historico_feeds[url]['ultima_actualizacion'] = None
                    historico_feeds[url]['delay'] = None
                    historico_feeds['modified'] = True
                # end if
                semaforo.release()

                ultimo_check           = historico_feeds[url]['ultimo_check']
                proximo_check          = historico_feeds[url]['proximo_check']
                ultima_actualizacion   = historico_feeds[url].get('ultima_actualizacion', None)
                delay                  = historico_feeds[url].get('delay', None)

                ahora = datetime.now()
                if proximo_check and ahora < proximo_check:
                    continue
                # end if

                title = feed.get('title', feed.get('text', url))
                mylog.debug ('Processing '+title)

                email = feed.get('ownerEmail', None)
                if email:
                    #mylog.debug ('email[0]=' + _email_destino[0] + ', email[1]=' + _email_destino[1])
                    #mylog.debug ('Overriding email: ' +email)
                    email_destino = _email_destino[0], email
                else:
                    email_destino = _email_destino
                # end if


                auth = feed.get('auth', None)
                if auth:
                    if ':' in auth:
                        username, password = auth.split(':')
                    else:
                        mylog.error ('The "auth" parameter for the feed '+title+' is invalid')
                        continue
                    # end if
                else:
                    username, password = None, None
                # end if
                
                xml = None
                try:
                    xml = cache.feed_parse(url, config['can_pipe'] == '1', username, password)
                except socket.timeout:
                    mylog.info ('Timeout error downloading %s' % url)
                    mylog.debug ('Will retry in the the next pass')
                    continue
                except HTTPError, e:
                    mylog.info ('HTTP Error %d downloading %s' % (e.code, url,))
                except URLError, e:
                    mylog.info ('URLError (%s) downloading %s' % (e.reason, url,))
                except OfflineError:
                    mylog.info ('Resource unavailable when offline (%s)' % url)
                except Exception, e:
                    mylog.exception ('Error %s downloading %s' % (str(e), url))

                if xml:
                    mylog.debug (xml['channel']['Cache-Result'] + ' ' + url)
                    channel = Channel(title, xml['channel'], url, feed['htmlUrl'], feed['download_link'] == '1', feed['diff'] == '1', feed['download_images'] == '1', feed)
                    for elemento in xml['items']:
                        item = channel.NewItem(elemento, xml["encoding"], feed['remove'])
                        
#                         for k in item.keys():
#                             mylog.debug('Key: ' + str(k))

                        if historico_posts.has_key(item.urlHash):
                            historico_posts[item.urlHash]['timestamp'] = datetime.now()
                            historico_posts['modified'] = True

                            check_text = feed['check_text'] == '1'

                            if check_text:
                                if item.texto_nuevo.strip() == historico_posts[item.urlHash]['text'].strip():
                                    continue
                                # end if
                            else:
                                continue
                            # end if

                            item.is_modified = 'True'
                        else:
                            item.is_modified = 'False'
                        # end if

                        items.append(item)
                    # end for
                # end if xml:

                if items:
                    mylog.info ('%d new items in %s' % (items.__len__(),title))
                else:
                    mylog.debug ('No change in %s' % (title,))
                # end if

                items_sin_agrupar = items[:]

                if (len(items) >= 1) and (feed['digest'] == '1'):
                    lista_vieja = items[:]
                    items = [AgruparItems(lista_vieja, feed['titles'] == '1', config['encoding'], config['reverse'] == '1')]
                # end if

                email_ok = True
                envio = config.get( 'sender', email_destino[1] )
                if(config['multipart'] == 'off'):
                     format = "html"
                else:
                     format = "multipart"
                if((config['textonly'] == '1') or (feed['textonly'] == '1')):
                    format = "plaintext"
                    
                encoding = config['encoding']
                include_threading = config['threading'] == '1'
                subject_prefix = config['subject']

                for item in items:
                    self.email_queue.put(item.GetEmail(envio, email_destino, format, encoding, include_threading, subject_prefix, config['from_address']))
                # end for

                # second pass for mobile copy, provided we could send the first one
                if( (feed['mobile'] == '1' ) and movil_destino and email_ok ):
                    send = False
                    
                    time = feed.get('mobile_time', None)
                    if time:
                        parsed_time = parseTimeRange(time)
                        if parsed_time:
                            if checkTime (parsed_time):
                                send = True
                        else:
                            mylog.error ('Error parsing the time range "%s" in the feed %s' % (time, url))
                    
                    if send:
                        for item in items:
                            self.email_queue.put(item.GetEmail(envio, movil_destino, "plaintext", encoding, include_threading, subject_prefix))
                        # end for
                    # end if
                # end if

                if email_ok:
                    for item in items_sin_agrupar:
                        historico_posts[item.urlHash] = {'text':item.texto_nuevo, 'timestamp':datetime.now()}
                        historico_posts['modified'] = True
                    # end for

                    # get the time until next check, 60 minutos by default
                    delay = int(feed['delay'])

                    ###semaforo.acquire()
                    historico_feeds[url]['ultimo_check'] = datetime.now()
                    historico_feeds[url]['proximo_check'] = datetime.now() + timedelta(minutes=delay)
                    if items.__len__() > 0:
                        historico_feeds[url]['ultima_actualizacion'] = datetime.now()
                    historico_feeds[url]['delay'] = delay
                    historico_feeds['modified'] = True
                    ###semaforo.release()
                # end if
            except:
                mylog.exception ('Exception processing '+url)
        # end while
    # end def
# end class

log = None

def setPriority (priority):
    # 0 = Low priority
    # 1 = Normal priority
    # 2 = High priority
    
    if priority == 1:
        pass
    elif priority == 2:
        raise NotImplementedError('High priority mode not implemented yet')
    elif priority == 0:
        if sys.platform.lower().startswith('win'):
            try: 
                import ctypes
                kernel32 = ctypes.windll.kernel32
                thread = kernel32.GetCurrentThread()
                kernel32.SetThreadPriority(thread, -15)
                log.debug ("Thread priority lowered.")
            except ImportError: 
                log.error ('CTypes module is not available. The parameter "priority" will be ignored')
                pass
        else:
            raise NotImplementedError ('Priority settings only implemented in Windows')
    else:
        raise ValueError ('The parameter "priority" has an invalid value (%d)' % priority)
    

def MainLoop():
    global historico_posts
    global historico_feeds
    global cache
    global log
    global DEBUG

    semaforo = _threading.BoundedSemaphore()
    historico_feeds, historico_posts = None, None

    while True:
        config = LeerConfig()

        DEBUG = config['debug'] == '1'
    
        if not log:
            log_dir = os.path.normpath(os.path.join(GetHomeDir(), '.newspipe/log'))
            log = LogFile(config['log_console']  == '1', 'newspipe', log_dir, DEBUG)        
        # end if
        gc.collect()

        if DEBUG:
            mylog.warning ('DEBUG MODE')
        # end if

        mylog.debug ('Home directory: '+GetHomeDir())

        try:
            mylog.debug ('Configuration settings:')
            mylog.debug ('-'*30)
            for x,y in config.items():
                mylog.debug ('%s: %s', x, y)
            # end for
            mylog.debug ('-'*30)
            
            setPriority (int(config['priority']))

            cache.offline = config['offline'] == '1'
            if cache.offline:
                mylog.warning('Working offline')
            # end if

            cache.debug = DEBUG

            if CheckOnline(config):
                NUM_WORKERS = int(config['workers'])
                
                if not has_threading:
                    log.warning ('Running without threads support')
                    NUM_WORKERS = 1

                archivo = config['opml']

                opml = None
                try:
                    source_path = os.path.split(sys.argv[0])[0]
                    for p in ('.', source_path):
                        if os.path.exists (os.path.join(p, archivo)):
                            archivo = os.path.join(p, archivo)
                            break
                            
                    fp = cache.urlopen(archivo, max_age=60, can_pipe=False).content
                    opml = AplanarArbol(ParseOPML(fp), OPML_DEFAULTS)
                    mylog.debug ('Processing file: '+archivo)
                except URLError:
                    mylog.error ('Cannot find the opml file: '+archivo)
                    opml = None
                except:
                    mylog.exception ('Error parsing file: '+archivo)
                    opml = None

                if opml:
                    email_destino = (opml['head']['ownerName'].strip('"'), opml['head']['ownerEmail'])
                    if( opml['head'].has_key('ownerMobile') ):
                        movil_destino = (opml['head']['ownerName'].strip('"'), opml['head']['ownerMobile'])
                    else:
                        movil_destino = False

                    if opml['head'].has_key('fromEmail'):
                        name = opml['head'].get('fromName', 'Newspipe')
                        from_address = name.strip('"') + ' <' + opml['head']['fromEmail'] + '>'
                        config['from_address'] = from_address
                        
                    if not historico_feeds or not historico_posts:
                        historico_feeds, historico_posts = CargarHistoricos(opml['head']['title'])

                    feeds_queue = Queue.Queue(0)
                    email_queue = Queue.Queue(0)

                    log.debug ('Inserting the feeds into the pending queue')
                    for feed in opml['body']:
                        if feed['active'] == '1':
                            feeds_queue.put(feed)
                        else:
                            log.debug ('Ignoring the Inactive feed: '+feed['xmlUrl'])
                    # end for

                    log.debug ('Inserting the end-of-work markers in the queue')
                    for x in range(NUM_WORKERS):
                        feeds_queue.put(None)
                    # end for

                    log.debug ('Starting working threads')
                    workers = []
                    for x in range(NUM_WORKERS):
                        w = FeedWorker (feeds_queue, email_queue, config, email_destino, movil_destino, semaforo)
                        workers.append(w)
                        w.start()
                    # end for

                    log.debug ('Waiting for all the threads to finish')
                    for w in workers:
                        w.join()
                    # end for                

                    log.debug ('Extracting the emails from the results queue')
                    emails = []
                    while True:
                        try:
                            email = email_queue.get_nowait()
                            emails += [email,]
                        except Queue.Empty:
                            break
                        # end try
                    # end while

                    try:
                        EnviarEmails (emails, config['send_method'], config['smtp_server'], config['smtp_auth'] == '1',config['smtp_user'],config['smtp_pass'], config['procmail'], config['reverse'] == '1', config['smtp_port'], config['smtp_tls'], config['sender'])
                    except KeyboardInterrupt:
                        raise
                    except Exception, e:
                        mylog.exception ('Unhandled exception while sending emails')
                    # end try

                    mylog.debug (archivo + ' finished.')

                    # borrar las entradas del historico que son demasiado viejas
                    for hash, value in historico_posts.items():
                        if hash == 'modified':
                            continue
                        timestamp = value['timestamp']
                        delta = timedelta(days = 30) # borrar lo que tenga mas 30 dias de antiguedad - maybe this should be configurable too
                        if (datetime.now() - delta) > timestamp:
                            del historico_posts[hash]
                            historico_posts['modified'] = True
                        # end if
                    # end for
                    if historico_posts['modified']:
                        GrabarHistorico (historico_posts, opml['head']['title'], '.posts')
                    if historico_feeds['modified']:
                        GrabarHistorico (historico_feeds, opml['head']['title'], '.feeds')
                # end if
            # end if CheckOnline

            # erase from the cache anything older than 10 days - to be made configurable?
            try:
                cache.purge(10)
            except:
                mylog.exception ('Unhandled exception when purging the cache')
            # end try

            if int(config['sleep_time']) == 0:
                break
            else:
                del(historico_feeds)
                del(historico_posts)
                historico_feeds, historico_posts = None, None

                mylog.debug ('Going to sleep for %s minutes' % (config['sleep_time'],))
                try:
                    sleep(int(config['sleep_time'])*60)
                except KeyboardInterrupt:
                    return
                # end try
            # end if
        except:
            mylog.exception ('Unhandled exception')
            raise  # stop the loop, to avoid infinite exceptions loops ;)
    # end while
# end def



if __name__ == '__main__':
    print ABOUT_NEWSPIPE

    log = None
    mylog=MyLog()

    cache_dir = os.path.normpath(os.path.join(GetHomeDir(), '.newspipe/cache'))
    cache = Cache(cache_dir, agent=USER_AGENT)
    try:
        MainLoop()
    except KeyboardInterrupt:
        sys.exit(0)

